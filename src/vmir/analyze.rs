//! Static analyses over a raw `vmir::Program`, producing an
//! [`AnalyzedProgram`].
//!
//! Currently the only analysis is the verification order: dependencies are
//! scheduled before dependents, ties break in program order, and methods
//! (always sinks) fall out last. Programs whose resources depend on each
//! other circularly are rejected.

use std::cmp::Reverse;
use std::collections::{BinaryHeap, HashMap};

use petgraph::Direction::{Incoming, Outgoing};
use petgraph::algo::tarjan_scc;
use petgraph::graph::{DiGraph, NodeIndex};

use crate::vmir::{
    Declaration, InstExt, InstKind, Method, MemberId, Program, PureInst, ResourceBody,
};

/// A `Program` augmented with the results of static analyses. Extend with
/// further analysis fields as they are added.
#[derive(Debug, Clone)]
pub struct AnalyzedProgram {
    pub program: Program,
    /// Order in which schedulable members should be verified: every
    /// dependency precedes its dependents, methods last.
    pub order: Vec<MemberId>,
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
    let order = verification_order(&program)?;
    Ok(AnalyzedProgram { program, order })
}

/// Decide the order in which `program`'s declarations should be verified.
///
/// Returns the schedulable members (`Resource | Function | Method`) in an
/// order where every dependency precedes its dependents, with `MemberId`
/// (program order) as a deterministic tiebreak. Non-schedulable
/// declarations (domains, ADTs) are omitted. Returns
/// [`AnalysisError::CircularDependency`] if the dependency graph has a cycle.
fn verification_order(program: &Program) -> Result<Vec<MemberId>, AnalysisError> {
    let mut graph: DiGraph<MemberId, ()> = DiGraph::new();
    let mut node_of: HashMap<MemberId, NodeIndex> = HashMap::new();

    // One node per schedulable declaration.
    for (id, decl) in program.decls.iter_enumerated() {
        if is_schedulable(decl) {
            let n = graph.add_node(id);
            node_of.insert(id, n);
        }
    }

    // Edges: dependency -> dependent. Skip references to non-schedulable
    // declarations (e.g. `Type::Domain`).
    let mut deps = Vec::new();
    for (id, decl) in program.decls.iter_enumerated() {
        let Some(&dependent) = node_of.get(&id) else {
            continue;
        };
        deps.clear();
        decl_deps(decl, &mut deps);
        for dep in &deps {
            if let Some(&dependency) = node_of.get(dep) {
                graph.add_edge(dependency, dependent, ());
            }
        }
    }

    kahn(&graph).ok_or_else(|| cycle_error(program, &graph))
}

/// Kahn's algorithm with a program-order tiebreak. Returns `None` if the
/// graph contains a cycle (fewer nodes emitted than present).
fn kahn(graph: &DiGraph<MemberId, ()>) -> Option<Vec<MemberId>> {
    // Indegree = number of unverified dependencies (incoming edges).
    let mut indegree: HashMap<NodeIndex, usize> = graph
        .node_indices()
        .map(|n| (n, graph.neighbors_directed(n, Incoming).count()))
        .collect();

    // Min-heap on the member id keeps the ready set in program order.
    let mut ready: BinaryHeap<Reverse<(MemberId, NodeIndex)>> = graph
        .node_indices()
        .filter(|n| indegree[n] == 0)
        .map(|n| Reverse((graph[n], n)))
        .collect();

    let mut order = Vec::with_capacity(graph.node_count());
    while let Some(Reverse((id, n))) = ready.pop() {
        order.push(id);
        for succ in graph.neighbors_directed(n, Outgoing) {
            let d = indegree.get_mut(&succ).unwrap();
            *d -= 1;
            if *d == 0 {
                ready.push(Reverse((graph[succ], succ)));
            }
        }
    }

    (order.len() == graph.node_count()).then_some(order)
}

/// Build a `CircularDependency` error naming the members of a cycle.
fn cycle_error(program: &Program, graph: &DiGraph<MemberId, ()>) -> AnalysisError {
    let mut names = Vec::new();
    for scc in tarjan_scc(graph) {
        let cyclic = scc.len() > 1 || graph.contains_edge(scc[0], scc[0]);
        if cyclic {
            for n in scc {
                names.push(program.interner.resolve(&graph[n]).to_string());
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
            if let Some((req, _)) = &r.requires {
                out.push(*req);
            }
            if let Some(body) = &r.body {
                resource_body_deps(body, out);
            }
        }
        Declaration::Method(m) => method_deps(m, out),
        // Functions have no body yet; nothing to depend on.
        Declaration::Function(_)
        | Declaration::Domain(_)
        | Declaration::DomainElement
        | Declaration::Adt(_)
        | Declaration::AdtConstructor => {}
    }
}

fn resource_body_deps(body: &ResourceBody, out: &mut Vec<MemberId>) {
    // Resource bodies use `ResourceCtx` (`InstExt = !`): the only member
    // references are `FunctionCall`s (e.g. `@addr` functions).
    for inst in &body.insts {
        if let InstKind::Pure(_, PureInst::FunctionCall(_, fc)) = &inst.kind {
            out.push(fc.function);
        }
    }
}

fn method_deps(m: &Method, out: &mut Vec<MemberId>) {
    for inst in &m.insts {
        match &inst.kind {
            InstKind::Pure(_, PureInst::FunctionCall(_, fc)) => out.push(fc.function),
            InstKind::Ext(InstExt::ResourceCall(c)) => out.push(c.resource),
            _ => {}
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::vmir::{
        HeapVal, Inst, InstKind, MethodInst, PathConds, Resource, ResourceCall,
    };
    use lasso::Rodeo;
    use typed_index_collections::TiVec;

    fn resource_requiring(req: Option<MemberId>) -> Declaration {
        Declaration::Resource(Resource {
            params: vec![],
            requires: req.map(|r| (r, vec![])),
            body: None,
        })
    }

    fn method_calling(res: MemberId) -> Declaration {
        let call = ResourceCall {
            resource: res,
            ctx_heap: HeapVal::Empty,
            args: vec![],
        };
        let inst: MethodInst = Inst {
            pc: PathConds::default(),
            kind: InstKind::Ext(InstExt::ResourceCall(call)),
        };
        Declaration::Method(Method { insts: vec![inst] })
    }

    fn program(names: &[&str], decls: Vec<Declaration>) -> Program {
        let mut interner: Rodeo<MemberId> = Rodeo::new();
        for name in names {
            interner.get_or_intern(name);
        }
        Program {
            decls: TiVec::from(decls),
            interner,
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
        assert_eq!(analyzed.order, vec![c, b, a, MemberId(3)]);
    }

    #[test]
    fn independent_nodes_keep_program_order() {
        // Three independent resources: order is just program order.
        let prog = program(
            &["A", "B", "C"],
            vec![
                resource_requiring(None),
                resource_requiring(None),
                resource_requiring(None),
            ],
        );
        let analyzed = analyze(prog).expect("acyclic");
        assert_eq!(analyzed.order, vec![MemberId(0), MemberId(1), MemberId(2)]);
    }
}
