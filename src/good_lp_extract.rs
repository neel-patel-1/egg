use good_lp::{
    variables,
    variable,
    Variable,
    ProblemVariables,
    default_solver,
    Solution,
    SolverModel,
    Expression
};
use std::collections::HashMap;
use smallvec::SmallVec;

use crate::*;

pub struct GoodLpExtractor<'a, L:Language, N:Analysis<L>> {
    vars: ProblemVariables,
}


impl <'a, L, N> GoodLpExtractor<'a, L, N>
where
    L: Language,
    N: Analysis<L>,
{

    pub fn new<CF>(egraph: &'a EGraph<L, N>, cost_function: CF) -> Self
    where
        CF: CostFunction<L>,
    {
        let mut vars = variables!();
        let enode_vars: HashMap<(Id, usize), Variable> = HashMap::new();
        Self {
            vars
        }
    }

    pub fn solve(mut self, eclass: Id) -> (f64, RecExpr<L>) {
        return (0.0, RecExpr::default());
    }
}