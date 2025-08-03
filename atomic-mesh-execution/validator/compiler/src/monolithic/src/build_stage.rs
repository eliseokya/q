//! Build expression stage (extracted from build-expression component)

use common::{CompilerError, PipelineData, TypedAction, Expr, Action, Chain, build_errors};

pub fn process(pipeline_data: &mut PipelineData) -> Result<(), CompilerError> {
    let typed_actions = pipeline_data.typed_actions.as_ref().ok_or_else(|| {
        CompilerError::new(
            "monolithic-build",
            build_errors::MISSING_TYPED_ACTIONS,
            "No typed actions in pipeline data".to_string()
        )
    })?;

    // Analyze parallel opportunities (simplified for performance)
    let parallel_groups = analyze_parallel_opportunities(typed_actions)?;

    // Build expression tree
    let expr = build_expression_tree(typed_actions, &parallel_groups)?;

    // Optimize expression  
    let optimized_expr = optimize_expression(expr)?;

    pipeline_data.expr = Some(optimized_expr);
    Ok(())
}

#[derive(Debug, Clone)]
struct ParallelGroup {
    start_index: usize,
    end_index: usize,
    actions: Vec<usize>,
}

fn analyze_parallel_opportunities(actions: &[TypedAction]) -> Result<Vec<ParallelGroup>, CompilerError> {
    // Simplified parallel analysis for performance
    // Only look for consecutive same-chain actions with no dependencies
    
    if actions.len() < 2 {
        return Ok(vec![]);
    }

    let mut groups = Vec::new();
    let mut current_group = vec![0];
    
    for i in 1..actions.len() {
        // Check if action i can be parallel with previous actions
        if can_parallelize_simple(&actions[i-1], &actions[i]) {
            current_group.push(i);
        } else {
            // Finalize current group if it has 2+ actions
            if current_group.len() >= 2 {
                groups.push(ParallelGroup {
                    start_index: current_group[0],
                    end_index: *current_group.last().unwrap(),
                    actions: current_group.clone(),
                });
            }
            current_group = vec![i];
        }
    }

    // Handle final group
    if current_group.len() >= 2 {
        groups.push(ParallelGroup {
            start_index: current_group[0],
            end_index: *current_group.last().unwrap(),
            actions: current_group,
        });
    }

    Ok(groups)
}

fn can_parallelize_simple(action1: &TypedAction, action2: &TypedAction) -> bool {
    // Simple heuristic: same chain, no bridges, different tokens
    if action1.chain != action2.chain {
        return false;
    }

    // No bridges
    if matches!(&action1.action, Action::Bridge { .. }) || matches!(&action2.action, Action::Bridge { .. }) {
        return false;
    }

    // For swaps, check token overlap (simplified)
    if let (Action::Swap { token_in: in1, token_out: out1, .. }, 
            Action::Swap { token_in: in2, token_out: out2, .. }) = (&action1.action, &action2.action) {
        // Allow if no token overlap
        return in1 != in2 && in1 != out2 && out1 != in2 && out1 != out2;
    }

    true
}

fn build_expression_tree(actions: &[TypedAction], parallel_groups: &[ParallelGroup]) -> Result<Expr, CompilerError> {
    if actions.is_empty() {
        return Err(CompilerError::new(
            "monolithic-build",
            build_errors::EMPTY_ACTIONS,
            "Cannot build expression from empty action list".to_string()
        ));
    }

    // Simple sequential building for performance
    let mut expr = create_action_expr(&actions[0]);

    for action in actions.iter().skip(1) {
        let action_expr = create_action_expr(action);
        expr = Expr::Seq {
            e1: Box::new(expr),
            e2: Box::new(action_expr),
        };
    }

    // Wrap in chain context
    let chain = actions[0].chain.clone().unwrap_or(Chain::Polygon);
    Ok(Expr::OnChain {
        chain,
        expr: Box::new(expr),
    })
}

fn create_action_expr(typed_action: &TypedAction) -> Expr {
    Expr::Action {
        action: typed_action.action.clone(),
    }
}

fn optimize_expression(expr: Expr) -> Result<Expr, CompilerError> {
    // Simplified optimization for performance
    // Just return the expression as-is for now
    Ok(expr)
}