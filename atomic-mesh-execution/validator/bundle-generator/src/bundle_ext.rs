//! Extension methods for common Bundle type

use common::types::{Bundle, Expr, Action};

/// Extension trait for Bundle
pub trait BundleExt {
    fn get_first_action(&self) -> Option<&Action>;
    fn collect_actions(&self) -> Vec<Action>;
}

impl BundleExt for Bundle {
    fn get_first_action(&self) -> Option<&Action> {
        get_first_action_from_expr(&self.expr)
    }
    
    fn collect_actions(&self) -> Vec<Action> {
        let mut actions = Vec::new();
        collect_actions_from_expr(&self.expr, &mut actions);
        actions
    }
}

fn get_first_action_from_expr(expr: &Expr) -> Option<&Action> {
    match expr {
        Expr::Action { action } => Some(action),
        Expr::Seq { first, second: _ } => get_first_action_from_expr(first),
        Expr::Parallel { exprs } => exprs.first().and_then(|e| get_first_action_from_expr(e)),
        Expr::OnChain { chain: _, expr } => get_first_action_from_expr(expr),
    }
}

fn collect_actions_from_expr(expr: &Expr, actions: &mut Vec<Action>) {
    match expr {
        Expr::Action { action } => actions.push(action.clone()),
        Expr::Seq { first, second } => {
            collect_actions_from_expr(first, actions);
            collect_actions_from_expr(second, actions);
        }
        Expr::Parallel { exprs } => {
            for e in exprs {
                collect_actions_from_expr(e, actions);
            }
        }
        Expr::OnChain { chain: _, expr } => collect_actions_from_expr(expr, actions),
    }
}