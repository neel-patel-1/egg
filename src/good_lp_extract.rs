use good_lp::{
    variables,
    variable,
    Variable,
    ProblemVariables,
    variable::UnsolvedProblem,
    Solution,
    SolverModel,
    Constraint,
    Expression
};
#[cfg(feature = "clarabel")]
use good_lp::clarabel;
#[cfg(feature = "cbc")]
use good_lp::coin_cbc;
#[cfg(feature = "highs")]
use good_lp::highs as highs;
#[cfg(feature = "microlp")]
use good_lp::microlp;
#[cfg(feature = "lpsolve")]
use good_lp::lp_solve;
#[cfg(feature = "scip")]
use good_lp::scip;
#[cfg(any(feature = "highs", feature = "cbc"))]
use good_lp::WithTimeLimit;
use std::collections::HashMap;
use smallvec::SmallVec;

use crate::*;

/// A structure to perform extraction using integer linear programming.
/// This uses the [`good_lp`]() library.
/// Any of its available solvers can be used by enabling one of the available features in the Cargo.toml.
pub struct GoodLpExtractor<'a, L:Language, N:Analysis<L>> {
    egraph: &'a EGraph<L, N>,
    enode_vars: HashMap<(Id, usize), Variable>,
    vars: ProblemVariables,
    constraints: Vec<Constraint>,
    total_cost: Expression,
}


impl <'a, L, N> GoodLpExtractor<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{

    /// Create a [`GoodLpExtractor`] and most of the variables and constraints for the ILP formulation of the extraction problem.
    /// See those docs for details.
    pub fn new<CF>(egraph: &'a EGraph<L, N>, mut cost_function: CF) -> Self
    where
        CF: LpCostFunction<L, N>,
    {
        let mut vars = variables!();
        let mut constraints = Vec::new();
        let mut total_cost: Expression = 0.into();
        let mut enode_vars: HashMap<(Id, usize), Variable> = HashMap::new();

        /* t_m */
        let mut topo_vars: HashMap<Id, Variable> = HashMap::new();
        for class in egraph.classes() {
            let t_m = vars.add(variable().min(0.0).max(1.0));
            topo_vars.insert(class.id, t_m);
        }
        const EPS: f64 = 1e-3;
        const ALPHA: f64 = 2.0;

        /* pass over e-graph creating binary variables constraints */
        for class in egraph.classes() {
            let t_parent = topo_vars[&class.id].clone();
            for (node_index, _node) in class.nodes.iter().enumerate() {
                let node_var = *enode_vars
                    .entry((class.id, node_index))
                    .or_insert_with(|| vars.add(variable().binary()));
                for child in class.nodes[node_index].children() {
                    let child_class = egraph.find(*child);
                    let mut child_vars = Vec::new();
                    /* ensure every enode in the child e‑class has a variable */
                    for (c_idx, _c_node) in egraph[child_class].nodes.iter().enumerate() {
                        let var = enode_vars
                            .entry((child_class, c_idx))
                            .or_insert_with(|| vars.add(variable().binary()))
                            .clone();
                        child_vars.push(var);
                    }

                    /* node_var ≤ Σ child_vars  */
                    let child_sum: Expression = child_vars.iter().cloned().sum();
                    constraints.push(Into::<Expression>::into(node_var.clone()).leq(child_sum));

                    #[cfg(not(feature = "no_acyclic"))]
                    {
                        let node_expr: Expression = node_var.clone().into();
                        let t_child = topo_vars[&child_class].clone();
                        let big_m_part: Expression = (Into::<Expression>::into(1.0) - node_expr.clone()) * ALPHA;
                        let acyc_expr: Expression = t_parent.clone() - t_child - (Into::<Expression>::into(EPS)) + big_m_part;
                        constraints.push(Into::<Expression>::into(acyc_expr).geq(Into::<Expression>::into(0)));
                    }
                }
                let cost = cost_function.node_cost(egraph, class.id, _node);

                total_cost += cost * node_var;
            }
        }
        Self {
            egraph,
            enode_vars,
            vars,
            constraints,
            total_cost,
        }
    }

    /// Add the root node selection constraint for the root provided, solve the ILP formulation of the extraction problem, build a recursive expression from the solution, and return the cost and expression.
    pub fn solve(mut self, eclass: Id, solver_choice: String, timeout: u64) -> (f64, RecExpr<L>) {
        let root_class_id = self.egraph.find(eclass);
        println!("Num Classes: {} Root Class: {}", self.egraph.classes().len(), root_class_id);
        let root_class = &self.egraph[root_class_id];
        let root_vars = root_class
            .nodes
            .iter()
            .enumerate()
            .map(|(node_index, _)| self.enode_vars[&(root_class_id, node_index)].clone())
            .collect::<Vec<_>>();

       self.constraints.push(root_vars.iter().cloned().sum::<Expression>().eq(1));

        println!("Root vars: {:?}", root_vars);
        let problem: UnsolvedProblem = self.vars
            .minimise(&self.total_cost);

        match solver_choice.as_str() {
            #[cfg(feature = "clarabel")]
            "clarabel" => {
                let solution = problem
                    .using(clarabel)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );

                (obj_cost, rexpr)
            },
            #[cfg(feature = "highs")]
            "highs" => {
                let solution = problem
                    .using(highs)
                    .with_time_limit(timeout as f64)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );

                (obj_cost, rexpr)
            },
            #[cfg(feature = "cbc")]
            "cbc" => {
                let solution = problem
                    .using(coin_cbc)
                    .with_time_limit(timeout as f64)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );

                (obj_cost, rexpr)
            },
            #[cfg(feature = "lpsolve")]
            "lp_solve" => {
                let solution = problem
                    .using(lp_solve)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );
                (obj_cost, rexpr)
            },
            #[cfg(feature = "microlp")]
            "microlp" => {
                let solution = problem
                    .using(microlp)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );
                (obj_cost, rexpr)
            },
            #[cfg(feature = "scip")]
            "scip" => {
                let solution = problem
                    .using(scip)
                    .with_all(self.constraints)
                    .solve()
                    .unwrap();
                let obj_cost = solution.eval(&self.total_cost);
                let mut cache = HashMap::<Id, Id>::new();
                let mut rexpr = RecExpr::default();
                build(
                    self.egraph,
                    &self.enode_vars,
                    &solution,
                    root_class_id,
                    &mut cache,
                    &mut rexpr,
                );
                (obj_cost, rexpr)
            },
            _ => panic!("Unsupported solver: {}", solver_choice),
        }
    }
}

fn build<L, N>(
    egraph   : &EGraph<L, N>,
    enode_vs : &HashMap<(Id, usize), Variable>,
    sol      : &dyn Solution,
    class_id : Id,
    cache    : &mut HashMap<Id, Id>,
    out_expr : &mut RecExpr<L>,
) -> Id
where
    L: Language,
    N: Analysis<L>,
{
    if let Some(&id) = cache.get(&class_id) {
        return id;
    }
    // find the enode whose var == 1
    let class = &egraph[class_id];
    let (_, node) = class.nodes.iter().enumerate()
        .find(|(i, _)| sol.value(enode_vs[&(class_id, *i)]) > 0.5)
        .expect("no chosen node for e‑class");

    // recursively build children
    let new_children: SmallVec<[Id; 4]> = node
        .children()
        .iter()
        .map(|c| build(egraph, enode_vs, sol, egraph.find(*c), cache, out_expr))
        .collect();

    // add new node with mapped children
    let mut idx = 0usize;
    let mapped = node.clone().map_children(|_| {
        let id = new_children[idx];
        idx += 1;
        id
    });
    let new_id = out_expr.add(mapped);
    cache.insert(class_id, new_id);
    new_id
}