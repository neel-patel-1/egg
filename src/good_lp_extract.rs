use good_lp::{
    variables,
    variable,
    Variable,
    ProblemVariables,
    default_solver,
    Solution,
    SolverModel,
    Constraint,
    Expression
};
use std::collections::HashMap;
use smallvec::SmallVec;

use crate::*;

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
            vars,
            constraints,
            total_cost,
            enode_vars,
        }
    }

    pub fn solve(mut self, eclass: Id) -> (f64, RecExpr<L>) {
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
        let solution = self.vars
            .minimise(&self.total_cost)
            .using(default_solver)
            .with_all(self.constraints)
            .solve()
            .unwrap();
        let obj_cost = solution.eval(&self.total_cost);
    }
}