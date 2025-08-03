//! Build expression component - Third stage of the compiler pipeline
//! Builds DSL expression trees with parallel optimization

mod parallel_analyzer;
mod expression_builder;
mod optimizer;

use common::{
    CompilerError, PipelineData,
    errors::{read_stdin, write_stdout},
    build_errors
};

fn main() {
    // Read input from stdin
    let input = match read_stdin() {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "build-expression",
                "IO_ERROR",
                format!("Failed to read input: {}", e)
            ).exit(1);
        }
    };

    // Parse pipeline data
    let mut pipeline_data: PipelineData = match serde_json::from_str(&input) {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "build-expression",
                "PARSE_ERROR",
                format!("Failed to parse pipeline data: {}", e)
            ).exit(1);
        }
    };

    // Ensure we have typed actions to build from
    let typed_actions = match pipeline_data.typed_actions {
        Some(ref actions) => actions,
        None => {
            CompilerError::new(
                "build-expression",
                build_errors::MISSING_TYPED_ACTIONS,
                "No typed actions in pipeline data".to_string()
            ).exit(2);
        }
    };

    // Analyze for parallel execution opportunities
    let parallel_groups = match parallel_analyzer::analyze_parallel_opportunities(typed_actions) {
        Ok(groups) => groups,
        Err(e) => e.exit(3),
    };

    // Build expression tree
    let expr = match expression_builder::build_expression_tree(typed_actions, &parallel_groups) {
        Ok(expr) => expr,
        Err(e) => e.exit(4),
    };

    // Optimize expression
    let optimized_expr = match optimizer::optimize_expression(expr) {
        Ok(expr) => expr,
        Err(e) => e.exit(5),
    };

    // Update pipeline data
    pipeline_data.expr = Some(optimized_expr);

    // Write output to stdout
    if let Err(e) = write_stdout(&pipeline_data) {
        CompilerError::new(
            "build-expression",
            "OUTPUT_ERROR",
            format!("Failed to write output: {}", e)
        ).exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{Metadata, TypedAction, Action, Token, Protocol, Chain, Rational, Expr};
    use serde_json::json;

    fn create_typed_action(token_out: Token, chain: Chain) -> TypedAction {
        TypedAction {
            action: Action::Swap {
                amount_in: Rational::from_integer(100),
                token_in: Token::WETH,
                token_out,
                min_out: Rational::from_integer(0),
                protocol: Protocol::UniswapV2,
            },
            chain: Some(chain),
        }
    }

    #[test]
    fn test_simple_sequential() {
        let input = PipelineData {
            metadata: Metadata {
                opportunity_id: "test123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: None,
            typed_actions: Some(vec![
                create_typed_action(Token::USDC, Chain::Polygon),
                create_typed_action(Token::DAI, Chain::Polygon),
            ]),
            expr: None,
            constraints: json!({}),
        };

        // Process (in real execution this would go through main)
        let typed_actions = input.typed_actions.as_ref().unwrap();
        let parallel_groups = parallel_analyzer::analyze_parallel_opportunities(typed_actions).unwrap();
        let expr = expression_builder::build_expression_tree(typed_actions, &parallel_groups).unwrap();
        let optimized = optimizer::optimize_expression(expr).unwrap();

        // Should be sequential since second swap depends on USDC from first
        match optimized {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                assert!(matches!(*inner, Expr::Seq { e1: _, e2: _ }));
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }

    #[test]
    fn test_parallel_detection() {
        let input = PipelineData {
            metadata: Metadata {
                opportunity_id: "test123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: None,
            typed_actions: Some(vec![
                create_typed_action(Token::USDC, Chain::Polygon),
                create_typed_action(Token::WBTC, Chain::Polygon), // Independent, can parallelize
            ]),
            expr: None,
            constraints: json!({}),
        };

        let typed_actions = input.typed_actions.as_ref().unwrap();
        let parallel_groups = parallel_analyzer::analyze_parallel_opportunities(typed_actions).unwrap();
        
        // Should detect these can be parallel
        assert_eq!(parallel_groups.len(), 1);
        assert_eq!(parallel_groups[0].actions.len(), 2);

        let expr = expression_builder::build_expression_tree(typed_actions, &parallel_groups).unwrap();
        let optimized = optimizer::optimize_expression(expr).unwrap();

        match optimized {
            Expr::OnChain { chain: Chain::Polygon, expr: inner } => {
                assert!(matches!(*inner, Expr::Parallel { exprs: _ }));
            },
            _ => panic!("Expected OnChain wrapper with Parallel"),
        }
    }

    #[test]
    fn test_cross_chain_sequential() {
        let input = PipelineData {
            metadata: Metadata {
                opportunity_id: "test123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: None,
            typed_actions: Some(vec![
                create_typed_action(Token::USDC, Chain::Polygon),
                TypedAction {
                    action: Action::Bridge {
                        chain: Chain::Arbitrum,
                        token: Token::USDC,
                        amount: Rational::from_integer(100),
                    },
                    chain: Some(Chain::Polygon),
                },
                create_typed_action(Token::DAI, Chain::Arbitrum),
            ]),
            expr: None,
            constraints: json!({}),
        };

        let typed_actions = input.typed_actions.as_ref().unwrap();
        let parallel_groups = parallel_analyzer::analyze_parallel_opportunities(typed_actions).unwrap();
        
        // No parallel opportunities due to bridge
        assert_eq!(parallel_groups.len(), 0);

        let expr = expression_builder::build_expression_tree(typed_actions, &parallel_groups).unwrap();
        let optimized = optimizer::optimize_expression(expr).unwrap();

        // Should be fully sequential
        match optimized {
            Expr::OnChain { chain: _, expr: inner } => {
                // Check it's sequential structure
                fn count_seq_depth(expr: &Expr) -> usize {
                    match expr {
                        Expr::Seq { e1: _, e2 } => 1 + count_seq_depth(e2),
                        _ => 0,
                    }
                }
                assert_eq!(count_seq_depth(&inner), 2); // 3 actions = 2 Seq nodes
            },
            _ => panic!("Expected OnChain wrapper"),
        }
    }
}