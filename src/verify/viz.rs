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

use std::collections::{HashMap, HashSet};

use crate::verify::context::VerifyContext;
use crate::verify::heap::Heap;
use crate::verify::lang::Symbolic;
use crate::vmir::Type;

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
        let dir = crate::util::log_dir().map(|base| {
            let dir = PathBuf::from(base);
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

    /// Whether snapshots are being recorded (`SILVER_OXIDE_VIZ` set). Callers
    /// use this to skip building the snapshot inputs (heap clones, rendered
    /// instruction text) on the hot path.
    pub(crate) fn enabled(&self) -> bool {
        self.dir.is_some()
    }

    /// Record a snapshot of the current e-graph and the given labeled heaps
    /// (e.g. the two operands and result of a heap `add`/`sub`). The `label`
    /// becomes the page's top annotation; `highlight`, if set, is the value
    /// produced by the just-executed instruction — its e-class cluster is drawn
    /// highlighted.
    pub(crate) fn snapshot(
        &mut self,
        ctx: &VerifyContext<'_>,
        heaps: &[(String, Heap)],
        label: &str,
        highlight: Option<egg::Id>,
    ) {
        if self.dir.is_none() {
            return;
        }

        let step = self.pages.len();
        let mut dot = ctx
            .egraph
            .dot()
            .with_config_line("ranksep=1.2")
            // Global ranking so the heap cluster's `rank=source` reliably pins it
            // to the topmost rank on every page (stable position).
            .with_config_line("newrank=true")
            .to_string();

        // Rewrite each `FuncApp` node's label from the `fn<id>[tys]`
        // that `Symbolic`'s `Display` emits to the actual source function name
        // with type arguments (e.g. `name<tys>`). The rewrite is per *node*
        // (egg labels each as `<eclass>.<idx>`).
        let mut fresh: HashSet<u32> = HashSet::new();
        for class in ctx.egraph.classes() {
            for (idx, node) in class.nodes.iter().enumerate() {
                match node {
                    Symbolic::FuncApp(m, type_args, _) => {
                        let name = ctx.func_name(*m);
                        let label = if type_args.is_empty() {
                            name.to_string()
                        } else {
                            let args: Vec<String> =
                                type_args.iter().map(|t| ctx.type_name(t)).collect();
                            format!("{}<{}>", name, args.join(", "))
                        };
                        // egg renders the node as `<eclass>.<idx>[label = "<raw>"]`
                        // where `<raw>` is the node's `Display` (`fn<id>[tys]`).
                        let raw = node.to_string();
                        let needle = format!("{}.{idx}[label = \"{raw}\"]", usize::from(class.id));
                        let repl = format!(
                            "{}.{idx}[label = \"{}\"]",
                            usize::from(class.id),
                            escape(&label)
                        );
                        dot = dot.replace(&needle, &repl);
                    }
                    Symbolic::Fresh(u) => {
                        fresh.insert(*u);
                    }
                    _ => {}
                }
            }
        }
        // `Symbolic` renders a fresh value as `fresh<id>`; append its type from
        // the `fresh_types` oracle. Match the trailing `"` so `fresh1` doesn't
        // also rewrite `fresh10`.
        for u in fresh {
            if let Some(ty) = ctx.fresh_types.get(&u) {
                let label = format!("{}#{u}", ctx.type_name(ty));
                dot = dot.replace(&format!("fresh{u}\""), &format!("{}\"", escape(&label)));
            }
        }

        // Heap subgraphs (one per labeled heap), injected right after egg's
        // fixed opening line. Rename the graph so each page is a distinct
        // `digraph`.
        let header: String = heaps
            .iter()
            .enumerate()
            .map(|(i, (lbl, h))| heap_subgraph(ctx, i, lbl, h))
            .collect();
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

        // Per-eclass styling: background colored by type — reconstructed by
        // inference over the type-free e-graph plus the context's type oracle —
        // plus the const-fold value as the cluster label when known. egg opens
        // each cluster with `subgraph cluster_<id> {\n`; inject right after it
        // (cluster-scope `label` is the cluster's own, so no leakage).
        let mut type_memo: HashMap<egg::Id, Option<Type>> = HashMap::new();
        for class in ctx.egraph.classes() {
            let ty = crate::verify::types::infer_type(
                &ctx.egraph,
                &ctx.fresh_types,
                &ctx.func_ret_types,
                class.id,
                &mut type_memo,
            );
            let mut attrs = format!("    bgcolor=\"{}\"\n", cluster_color(ty.as_ref()));
            // Cluster label: the inferred type, plus the const-fold value when
            // known (two lines).
            let mut parts: Vec<String> = Vec::new();
            if let Some(t) = &ty {
                parts.push(escape(&ctx.type_name(t)));
            }
            if let Some(lit) = class.data.known() {
                parts.push(escape(&format!("= {lit}")));
            } else if class.data.is_inconsistent() {
                parts.push("⊥".to_string());
            }
            if !parts.is_empty() {
                attrs.push_str(&format!("    label=\"{}\"\n", parts.join("\\n")));
            }
            let needle = format!("subgraph cluster_{} {{\n", usize::from(class.id));
            if let Some(pos) = dot.find(&needle) {
                dot.insert_str(pos + needle.len(), &attrs);
            }
        }

        // Highlight the e-class the produced value landed in: a bold red border
        // (no fill, so the type color stays visible). Injected last so it wins.
        //
        // Skip constants: a produced value that folded to a literal (e.g. a
        // resource call whose contract boolean is the vacuous `true`) lives in
        // the shared global literal e-class, so a border + arg arrows out of it
        // are noise — every such step would mark the same node.
        if let Some(id) =
            highlight.filter(|id| ctx.egraph[ctx.egraph.find(*id)].data.known().is_none())
        {
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

/// Build one heap's `cluster_heap_<idx>` subgraph (titled `label`) plus edges
/// into the e-class clusters. `idx` namespaces the cluster and its chunk nodes
/// so several heaps (e.g. `add`'s two operands and result) can coexist on one
/// page. Every referenced id is canonicalized (`egraph.find`) so edges always
/// land on a live cluster even though the dump is un-saturated.
fn heap_subgraph(ctx: &VerifyContext<'_>, idx: usize, label: &str, heap: &Heap) -> String {
    let mut s = format!(
        "  subgraph cluster_heap_{idx} {{\n    label=\"{}\"\n    style=solid\n    rank=source\n",
        escape(label)
    );
    let mut edges = String::new();
    for (_, chunk) in heap.entries() {
        let c_addr = ctx.egraph.find(chunk.addr);
        let c_val = ctx.egraph.find(chunk.value);
        let c_perm = ctx.egraph.find(chunk.perm);
        let node = format!("chunk_{idx}_{}", usize::from(chunk.addr));
        s.push_str(&format!("    {node}[label=\"chunk\", shape=box]\n"));
        // Edges target an arbitrary node `.0` in the destination cluster.
        edges.push_str(&format!(
            "  {node} -> {ca}.0 [lhead=cluster_{ca}, color=blue, label=\"@\"]\n",
            ca = usize::from(c_addr),
        ));
        edges.push_str(&format!(
            "  {node} -> {cv}.0 [lhead=cluster_{cv}, color=black, label=\"v\"]\n",
            cv = usize::from(c_val),
        ));
        edges.push_str(&format!(
            "  {node} -> {cp}.0 [lhead=cluster_{cp}, color=red, label=\"p\"]\n",
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
        if run(
            "dot",
            &[
                "-Tpdf".as_ref(),
                dp.as_os_str(),
                "-o".as_ref(),
                pp.as_os_str(),
            ],
        ) {
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

/// Background color for an e-class cluster, keyed by its (inferred) type.
/// Primitives get distinct pastel hues; aggregate (`Domain`/`Addr`) and unknown
/// types stay gray.
fn cluster_color(ty: Option<&Type>) -> &'static str {
    match ty {
        Some(Type::Int) => "#cce5ff",  // blue
        Some(Type::Bool) => "#d4edda", // green
        Some(Type::Real) => "#fff3cd", // yellow
        Some(Type::Ref) => "#e2d4f0",  // purple
        _ => "#e0e0e0",                // gray: Domain/Addr or unknown
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
