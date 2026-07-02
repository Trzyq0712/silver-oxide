//! Static analyses over a raw `vmir::Program`, producing an
//! [`AnalyzedProgram`].
//!
//! Currently the only analysis is the verification order: dependencies are
//! scheduled before dependents, and methods (always sinks) fall out last.
//! Programs whose resources depend on each other circularly are rejected.

use petgraph::algo::{tarjan_scc, toposort};
use petgraph::prelude::DiGraphMap;

use crate::vmir::{
    Declaration, HeapInst, Inst, InstKind, MemberId, Method, Precond, Program, PureInst,
    ResourceBody, Type,
};

/// Dependency graph: node = schedulable `MemberId`, edge dependency ->
/// dependent. Acyclic once produced by [`analyze`].
pub type DepGraph = DiGraphMap<MemberId, ()>;

/// A `Program` augmented with the results of static analyses. Extend with
/// further analysis fields as they are added.
#[derive(Debug, Clone)]
pub struct AnalyzedProgram {
    pub program: Program,
    /// Acyclic dependency graph over schedulable members. The single source
    /// of truth for verification scheduling: a linear order is obtained by
    /// toposorting on demand; a parallel scheduler dispatches a node once all
    /// its dependencies are done.
    pub dep_graph: DepGraph,
}

#[derive(Debug)]
pub enum AnalysisError {
    /// Resources depend on each other circularly and cannot be ordered for
    /// verification. Carries the names of the members in the cycle.
    CircularDependency(Vec<String>),
}

impl std::fmt::Display for AnalysisError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::CircularDependency(names) => {
                write!(f, "circular resource dependency: {}", names.join(" -> "))
            }
        }
    }
}

/// Run all analyses over `program`, producing an [`AnalyzedProgram`].
pub fn analyze(program: Program) -> Result<AnalyzedProgram, AnalysisError> {
    let dep_graph = build_dep_graph(&program);
    // Toposort purely to validate acyclicity; the order itself is discarded
    // (consumers derive their own on demand).
    if toposort(&dep_graph, None).is_err() {
        return Err(cycle_error(&program, &dep_graph));
    }
    dump_callgraph(&dep_graph, &program);
    Ok(AnalyzedProgram { program, dep_graph })
}

/// Build the dependency graph over `program`'s schedulable members
/// (`Resource | Function | Method`). Edges run dependency -> dependent;
/// references to non-schedulable declarations (domains, ADTs) are dropped.
fn build_dep_graph(program: &Program) -> DepGraph {
    let mut graph = DepGraph::new();

    // One node per schedulable declaration.
    for (id, decl) in program.decls.iter_enumerated() {
        if is_schedulable(decl) {
            graph.add_node(id);
        }
    }

    // Edges: dependency -> dependent. Skip references to non-schedulable
    // declarations (which are not nodes).
    let mut deps = Vec::new();
    for (id, decl) in program.decls.iter_enumerated() {
        if !graph.contains_node(id) {
            continue;
        }
        deps.clear();
        decl_deps(decl, &mut deps);
        for &dep in &deps {
            if graph.contains_node(dep) {
                graph.add_edge(dep, id, ());
            }
        }
    }

    graph
}

/// Env-gated (`VIPER_DOT`) dump of the dependency graph to
/// `log_dir()/callgraph.dot` for debugging. Node labels are member names;
/// edges are unlabeled.
fn dump_callgraph(graph: &DepGraph, program: &Program) {
    use petgraph::dot::{Config, Dot};

    if std::env::var("VIPER_DOT").is_err() {
        return;
    }
    let edge_attr = |_, _| String::new();
    let node_attr = |_, (id, _): (MemberId, &MemberId)| format!("label = \"{}\"", program.name(id));
    let dot = Dot::with_attr_getters(
        graph,
        &[Config::EdgeNoLabel, Config::NodeNoLabel],
        &edge_attr,
        &node_attr,
    );
    let dir = crate::util::log_dir();
    let path = format!("{dir}/callgraph.dot");
    if let Err(e) =
        std::fs::create_dir_all(&dir).and_then(|()| std::fs::write(&path, format!("{dot:?}")))
    {
        eprintln!("failed to write {path}: {e}");
    }
}

/// Build a `CircularDependency` error naming the members of a cycle.
fn cycle_error(program: &Program, graph: &DepGraph) -> AnalysisError {
    let mut names = Vec::new();
    for scc in tarjan_scc(graph) {
        let cyclic = scc.len() > 1 || graph.contains_edge(scc[0], scc[0]);
        if cyclic {
            for id in scc {
                names.push(program.name(id).to_string());
            }
        }
    }
    AnalysisError::CircularDependency(names)
}

fn is_schedulable(decl: &Declaration) -> bool {
    matches!(
        decl,
        Declaration::Resource(_) | Declaration::Function(_) | Declaration::Method(_)
    )
}

/// Collect the `MemberId`s a declaration depends on (must be verified
/// first). Domain/ADT references are included verbatim; the caller drops
/// any that aren't schedulable nodes.
fn decl_deps(decl: &Declaration, out: &mut Vec<MemberId>) {
    match decl {
        Declaration::Resource(r) => {
            if let Precond::Ctx(req, _) = &r.precond {
                out.push(*req);
            }
            if let Some(body) = &r.body {
                resource_body_deps(body, out);
            }
        }
        Declaration::Method(m) => method_deps(m, out),
        Declaration::Function(f) => {
            // A function depends on every function it calls — including its own
            // `f#requires`/`f#ensures`, which are ordinary `Function` decls. This
            // orders callees before callers (so their bodies inline) and turns any
            // (mutual) recursion into a dependency cycle, rejected by `analyze`.
            if let Some(body) = &f.body {
                inst_deps(&body.insts, out);
            }
        }
        Declaration::DomainAxiom(ax) => inst_deps(&ax.body, out),
        // Leaf declarations: nothing to depend on.
        Declaration::Domain(_) | Declaration::Adt(_) => {}
    }
}

/// Collect the schedulable members referenced by an instruction stream: the
/// callee of each non-address `FunctionCall`, and the resource of each
/// inhale/exhale/fold/unfold/snap/from-snap. Shared by resource, method, and
/// function bodies.
///
/// An **address-typed** `FunctionCall` (result `Type::Addr`) is NOT a dependency:
/// forming an address needs no certificate, and a predicate's address function is
/// the predicate's own id, so treating it as a dependency would make a recursive
/// predicate (`acc(P(this.next))` in `P`'s body) a self-cycle.
fn inst_deps(insts: &[Inst], out: &mut Vec<MemberId>) {
    for inst in insts {
        match &inst.kind {
            InstKind::Pure(ty, PureInst::FunctionCall(fc)) if !matches!(ty, Type::Addr { .. }) => {
                out.push(fc.function)
            }
            InstKind::Heap(HeapInst::Inhale { call, .. } | HeapInst::Exhale { call, .. }) => {
                out.push(call.resource)
            }
            InstKind::Heap(HeapInst::Fold { call, .. } | HeapInst::Unfold { call, .. }) => {
                out.push(call.resource)
            }
            // Snapshot narrowing/widening needs the resource's certificate
            // (footprint layout), so the resource must be verified first.
            InstKind::Pure(_, PureInst::Snap { resource, .. })
            | InstKind::Heap(HeapInst::FromSnap { resource, .. }) => out.push(*resource),
            _ => {}
        }
    }
}

fn resource_body_deps(body: &ResourceBody, out: &mut Vec<MemberId>) {
    inst_deps(&body.insts, out);
}

fn method_deps(m: &Method, out: &mut Vec<MemberId>) {
    inst_deps(&m.insts, out);
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::{
        HeapInst, HeapVal, Inst, InstKind, PathConds, Precond, Resource, ResourceCall, write,
    };
    use lasso::{Key, Rodeo};
    use std::collections::HashSet;
    use typed_index_collections::TiVec;

    fn resource_requiring(req: Option<MemberId>) -> Declaration {
        Declaration::Resource(Resource {
            name: lasso::Spur::try_from_usize(0).unwrap(),
            params: vec![],
            precond: match req {
                Some(r) => Precond::Ctx(r, vec![]),
                None => Precond::SelfFramed,
            },
            body: None,
        })
    }

    fn method_calling(res: MemberId) -> Declaration {
        let call = ResourceCall {
            resource: res,
            ctx_heap: None,
            args: vec![],
        };
        let inst: Inst = Inst {
            pc: PathConds::default(),
            heap: None,
            kind: InstKind::Heap(HeapInst::Inhale {
                base: HeapVal::Empty,
                call,
                perm: write(),
            }),
        };
        Declaration::Method(Method {
            name: lasso::Spur::try_from_usize(0).unwrap(),
            insts: vec![inst],
        })
    }

    fn program(names: &[&str], decls: Vec<Declaration>) -> Program {
        let mut interner = Rodeo::new();
        let mut name_ids = names.iter().map(|n| interner.get_or_intern(n));
        let mut final_decls = decls;
        for d in final_decls.iter_mut() {
            if let Some(n) = name_ids.next() {
                match d {
                    Declaration::Resource(r) => r.name = n,
                    Declaration::Method(m) => m.name = n,
                    Declaration::Function(f) => f.name = n,
                    Declaration::Adt(a) => a.name = n,
                    Declaration::Domain(do_) => do_.name = n,
                    Declaration::DomainAxiom(a) => a.name = Some(n),
                }
            }
        }
        Program {
            decls: TiVec::from(final_decls),
            interner,
            groups: Rodeo::new(),
        }
    }

    #[test]
    fn circular_resources_rejected() {
        // A requires B, B requires A.
        let a = MemberId(0);
        let b = MemberId(1);
        let prog = program(
            &["A", "B"],
            vec![resource_requiring(Some(b)), resource_requiring(Some(a))],
        );
        match analyze(prog) {
            Err(AnalysisError::CircularDependency(names)) => {
                assert!(names.contains(&"A".to_string()));
                assert!(names.contains(&"B".to_string()));
            }
            other => panic!("expected circular dependency, got {other:?}"),
        }
    }

    #[test]
    fn chain_then_method_last() {
        // A requires B, B requires C; method M calls A.
        let a = MemberId(0);
        let b = MemberId(1);
        let c = MemberId(2);
        let prog = program(
            &["A", "B", "C", "M"],
            vec![
                resource_requiring(Some(b)),
                resource_requiring(Some(c)),
                resource_requiring(None),
                method_calling(a),
            ],
        );
        let analyzed = analyze(prog).expect("acyclic");
        let m = MemberId(3);
        // Linear chain → unique topo order.
        let order = toposort(&analyzed.dep_graph, None).expect("acyclic");
        assert_eq!(order, vec![c, b, a, m]);
        // Stored graph carries the dependency edges.
        assert!(analyzed.dep_graph.contains_edge(c, b));
        assert!(analyzed.dep_graph.contains_edge(b, a));
        assert!(analyzed.dep_graph.contains_edge(a, m));
    }

    #[test]
    fn independent_nodes_all_scheduled() {
        // Three independent resources: all scheduled, order unconstrained.
        let prog = program(
            &["A", "B", "C"],
            vec![
                resource_requiring(None),
                resource_requiring(None),
                resource_requiring(None),
            ],
        );
        let analyzed = analyze(prog).expect("acyclic");
        let scheduled: HashSet<MemberId> = analyzed.dep_graph.nodes().collect();
        assert_eq!(
            scheduled,
            HashSet::from([MemberId(0), MemberId(1), MemberId(2)])
        );
    }
}
