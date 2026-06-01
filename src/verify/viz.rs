//! Per-instruction Graphviz snapshots of the e-graph + heap.
//!
//! Enabled by the `SILVER_OXIDE_VIZ` env var (its value is the output base
//! directory; empty → `./log`). Disabled = zero work beyond an env read at
//! method entry. One snapshot is taken after every executed instruction
//! (method body + resource bodies); each dumps the *raw* live e-graph (no
//! saturation) plus the latest heap as a `cluster_heap` subgraph whose chunk
//! nodes point at the relevant e-class clusters, and carries a top annotation
//! naming the instruction.
//!
//! All snapshots for one method are accumulated and emitted (on drop) as a
//! single **multi-page** PDF `<dir>/<method>.pdf` — one instruction per page,
//! with **variable page sizes** so a large e-graph isn't clipped. Each page is
//! rendered individually with `dot -Tpdf` (cairo sizes the page to the graph)
//! and the pages are merged with `pdfunite`. The combined `.dot` source is also
//! written. Best-effort: a missing `dot`/`pdfunite` leaves the `.dot` on disk.

use std::path::PathBuf;
use std::process::{Command, Stdio};

use crate::verify::context::VerifyContext;
use crate::verify::heap::Heap;
use crate::verify::lang;
use crate::vmir::{self, HeapInst, InstExt, InstKind, PureInst, Type};

pub(crate) struct Snapshotter {
    /// `None` = disabled (env var unset).
    dir: Option<PathBuf>,
    /// Filename-safe method name (output stem).
    method: String,
    /// One `digraph` per executed instruction, in execution order.
    pages: Vec<String>,
}

impl Snapshotter {
    pub(crate) fn from_env(method_name: &str) -> Self {
        let dir = std::env::var_os("SILVER_OXIDE_VIZ").map(|base| {
            let dir = if base.is_empty() {
                PathBuf::from("log")
            } else {
                PathBuf::from(base)
            };
            // Best-effort: a failed create just means later writes no-op-fail.
            let _ = std::fs::create_dir_all(&dir);
            dir
        });
        Self {
            dir,
            method: sanitize(method_name),
            pages: Vec::new(),
        }
    }

    /// Record a snapshot of the current e-graph and (optionally) a heap. The
    /// `label` becomes the page's top annotation; `highlight`, if set, is the
    /// value produced by the just-executed instruction — its e-class cluster is
    /// drawn highlighted.
    pub(crate) fn snapshot(
        &mut self,
        ctx: &VerifyContext<'_>,
        heap: Option<&Heap>,
        label: &str,
        highlight: Option<egg::Id>,
    ) {
        if self.dir.is_none() {
            return;
        }

        let step = self.pages.len();
        // Resolve `FuncApp` member ids to source names while rendering.
        let mut dot = {
            let _g = lang::with_interner(ctx.interner);
            ctx.egraph
                .dot()
                .with_config_line("ranksep=1.2")
                // Global ranking so the heap cluster's `rank=source` reliably
                // pins it to the topmost rank on every page (stable position).
                .with_config_line("newrank=true")
                .to_string()
        };

        // Heap subgraph: injected right after egg's fixed opening line. Rename
        // the graph so each page is a distinct `digraph`.
        let header = heap.map(|h| heap_subgraph(ctx, h)).unwrap_or_default();
        dot = dot.replacen(
            "digraph egraph {\n",
            &format!("digraph step_{step:03} {{\n{header}"),
            1,
        );

        // Page title: injected *after* all clusters (before the closing brace)
        // so the eclass clusters — defined earlier — don't inherit it as their
        // own label. A graph-scope `label` set before a subgraph leaks into it.
        let title = format!(
            "  labelloc=\"t\"\n  fontsize=20\n  label=\"#{step:03}  {}\"\n",
            escape(label)
        );
        if let Some(pos) = dot.rfind('}') {
            dot.insert_str(pos, &title);
        }

        // Per-eclass styling: background colored by type (primitives get a hue,
        // adt/domain stays gray) plus the const-fold value as the cluster label
        // when known. egg opens each cluster with `subgraph cluster_<id> {\n`;
        // inject right after it (cluster-scope `label` is the cluster's own, so
        // no leakage into nested content).
        for class in ctx.egraph.classes() {
            let data = &class.data;
            let mut attrs = format!("    bgcolor=\"{}\"\n", cluster_color(&data.ty));
            if let Some(lit) = &data.value {
                attrs.push_str(&format!("    label=\"= {}\"\n", escape(&lit.to_string())));
            }
            let needle = format!("subgraph cluster_{} {{\n", usize::from(class.id));
            if let Some(pos) = dot.find(&needle) {
                dot.insert_str(pos + needle.len(), &attrs);
            }
        }

        // Highlight the e-class the produced value landed in: a bold red border
        // (no fill, so the type color stays visible). Injected last so it wins.
        if let Some(id) = highlight {
            let canon = ctx.egraph.find(id);
            let needle = format!("subgraph cluster_{} {{\n", usize::from(canon));
            if let Some(pos) = dot.find(&needle) {
                dot.insert_str(
                    pos + needle.len(),
                    "    style=solid\n    color=red\n    penwidth=3\n",
                );
            }
        }

        self.pages.push(dot);
    }

    /// Concatenate all pages and render a single multi-page PDF (+ combined
    /// `.dot`). Best-effort. Called on drop so partial runs (e.g. an assertion
    /// failure mid-method) still emit everything up to the failure.
    fn finish(&self) {
        let Some(dir) = &self.dir else {
            return;
        };
        if self.pages.is_empty() {
            return;
        }
        // Keep the combined source for reference / manual rendering.
        let combined = self.pages.join("\n");
        let _ = std::fs::write(dir.join(format!("{}.dot", self.method)), &combined);

        render_pdf(dir, &self.method, &self.pages);
    }
}

impl Drop for Snapshotter {
    fn drop(&mut self) {
        self.finish();
    }
}

/// Build the `cluster_heap` subgraph plus edges into the e-class clusters.
/// Every referenced id is canonicalized (`egraph.find`) so edges always land
/// on a live cluster even though the dump is un-saturated.
fn heap_subgraph(ctx: &VerifyContext<'_>, heap: &Heap) -> String {
    let mut s = String::from(
        "  subgraph cluster_heap {\n    label=\"heap\"\n    style=solid\n    rank=source\n",
    );
    let mut edges = String::new();
    for (addr, chunk) in heap.entries() {
        let c_addr = ctx.egraph.find(addr);
        let c_val = ctx.egraph.find(chunk.value);
        let c_perm = ctx.egraph.find(chunk.perm);
        s.push_str(&format!(
            "    chunk_{a}[label=\"chunk\", shape=box]\n",
            a = usize::from(addr)
        ));
        // Edges target an arbitrary node `.0` in the destination cluster.
        edges.push_str(&format!(
            "  chunk_{a} -> {ca}.0 [lhead=cluster_{ca}, color=blue, label=\"@\"]\n",
            a = usize::from(addr),
            ca = usize::from(c_addr),
        ));
        edges.push_str(&format!(
            "  chunk_{a} -> {cv}.0 [lhead=cluster_{cv}, color=black, label=\"v\"]\n",
            a = usize::from(addr),
            cv = usize::from(c_val),
        ));
        edges.push_str(&format!(
            "  chunk_{a} -> {cp}.0 [lhead=cluster_{cp}, color=red, label=\"p\"]\n",
            a = usize::from(addr),
            cp = usize::from(c_perm),
        ));
    }
    s.push_str("  }\n");
    s.push_str(&edges);
    s
}

/// Best-effort multi-page render. `dot -Tpdf` (cairo) sizes each page to its
/// graph's bounding box but can't concatenate graphs, so render each page to
/// its own PDF (giving **variable page sizes** — large e-graphs aren't clipped)
/// then merge with `pdfunite`. Missing `dot`/`pdfunite` just leaves the `.dot`
/// on disk. Intermediate per-page files are cleaned up.
fn render_pdf(dir: &std::path::Path, method: &str, pages: &[String]) {
    let mut page_pdfs: Vec<PathBuf> = Vec::new();
    let mut tmp_dots: Vec<PathBuf> = Vec::new();

    for (i, page) in pages.iter().enumerate() {
        let dp = dir.join(format!(".{method}_{i:03}.dot"));
        let pp = dir.join(format!(".{method}_{i:03}.pdf"));
        if std::fs::write(&dp, page).is_err() {
            continue;
        }
        tmp_dots.push(dp.clone());
        if run("dot", &["-Tpdf".as_ref(), dp.as_os_str(), "-o".as_ref(), pp.as_os_str()]) {
            page_pdfs.push(pp);
        }
    }

    let out = dir.join(format!("{method}.pdf"));
    match page_pdfs.as_slice() {
        [] => {}
        // pdfunite needs ≥2 inputs; a lone page is just moved to the output.
        [single] => {
            let _ = std::fs::rename(single, &out);
        }
        _ => {
            let mut args: Vec<&std::ffi::OsStr> = page_pdfs.iter().map(|p| p.as_os_str()).collect();
            args.push(out.as_os_str());
            run("pdfunite", &args);
        }
    }

    for p in tmp_dots.iter().chain(page_pdfs.iter()) {
        let _ = std::fs::remove_file(p);
    }
}

/// Run a command to completion with no stdio. Returns `true` on exit code 0.
fn run(program: &str, args: &[&std::ffi::OsStr]) -> bool {
    Command::new(program)
        .args(args)
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false)
}

/// Background color for an e-class cluster, keyed by its type. Primitives get
/// distinct pastel hues; aggregate (`Domain`/`Addr`) types stay gray.
fn cluster_color(ty: &Type) -> &'static str {
    match ty {
        Type::Int => "#cce5ff",  // blue
        Type::Bool => "#d4edda", // green
        Type::Real => "#fff3cd", // yellow
        Type::Ref => "#e2d4f0",  // purple
        Type::Domain(_) | Type::Addr(_) => "#e0e0e0", // gray
    }
}

/// Filename-safe slug.
fn sanitize(s: &str) -> String {
    s.chars()
        .map(|c| if c.is_ascii_alphanumeric() { c } else { '_' })
        .collect()
}

/// Escape a string for use inside a dot `"..."` label.
fn escape(s: &str) -> String {
    s.replace('\\', "\\\\").replace('"', "\\\"")
}

/// Short label for a method instruction, used as the page annotation.
pub(crate) fn method_inst_label(
    kind: &InstKind<vmir::MethodCtx>,
    interner: &lasso::Rodeo<vmir::MemberId>,
) -> String {
    match kind {
        InstKind::Pure(_, pi) => format!("pure {}", pure_tag(pi)),
        InstKind::Heap(hi) => format!("heap {}", heap_tag(hi)),
        InstKind::Ext(InstExt::Assume(_)) => "assume".into(),
        InstKind::Ext(InstExt::Assert(_)) => "assert".into(),
        InstKind::Ext(InstExt::ResourceCall(call)) => {
            format!("rescall {}", interner.resolve(&call.resource))
        }
    }
}

/// Short label for a resource-body instruction (Ext is the never type here).
pub(crate) fn resource_inst_label(kind: &InstKind<vmir::ResourceCtx>) -> String {
    match kind {
        InstKind::Pure(_, pi) => format!("pure {}", pure_tag(pi)),
        InstKind::Heap(hi) => format!("heap {}", heap_tag(hi)),
        InstKind::Ext(never) => match *never {},
    }
}

fn pure_tag<P>(pi: &PureInst<P>) -> &'static str {
    match pi {
        PureInst::Fresh => "fresh",
        PureInst::Binary(..) => "binary",
        PureInst::Ternary(..) => "ternary",
        PureInst::Deref(..) => "deref",
        PureInst::FunctionCall(..) => "call",
        PureInst::Ext(_) => "ext",
    }
}

fn heap_tag<H>(hi: &HeapInst<H>) -> &'static str {
    match hi {
        HeapInst::Acc(_) => "acc",
        HeapInst::Add(..) => "add",
        HeapInst::Sub(..) => "sub",
        HeapInst::Ternary(..) => "ternary",
        HeapInst::Ext(_) => "ext",
    }
}
