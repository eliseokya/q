//! Transform actions component - Second stage of the compiler pipeline
//! Normalizes amounts and maps strings to typed enums

mod normalizer;
mod mapper;
mod chain_tracker;

use common::{
    CompilerError, PipelineData, TypedAction,
    errors::{read_stdin, write_stdout},
    transform_errors
};
use serde_json::Value;

fn main() {
    // Read input from stdin
    let input = match read_stdin() {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "transform-actions",
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
                "transform-actions",
                "PARSE_ERROR",
                format!("Failed to parse pipeline data: {}", e)
            ).exit(1);
        }
    };

    // Ensure we have actions to transform
    let actions = match pipeline_data.actions {
        Some(actions) => actions,
        None => {
            CompilerError::new(
                "transform-actions",
                transform_errors::MISSING_ACTIONS,
                "No actions array in pipeline data".to_string()
            ).exit(2);
        }
    };

    // Transform each action through the pipeline
    let mut typed_actions = Vec::new();
    
    for (index, action) in actions.iter().enumerate() {
        // 1. Normalize amounts
        let normalized = match normalizer::normalize_amounts(action, index) {
            Ok(normalized) => normalized,
            Err(e) => e.exit(3),
        };

        // 2. Map to typed action
        let typed_action = match mapper::map_to_typed(&normalized, index) {
            Ok(typed) => typed,
            Err(e) => e.exit(4),
        };

        typed_actions.push(typed_action);
    }

    // 3. Infer chain context
    let source_chain = pipeline_data.metadata.source_chain.as_deref();
    let actions_with_chains = match chain_tracker::infer_chains(typed_actions, source_chain) {
        Ok(actions) => actions,
        Err(e) => e.exit(5),
    };

    // Update pipeline data
    pipeline_data.actions = None; // Clear raw actions
    pipeline_data.typed_actions = Some(actions_with_chains);

    // Write output to stdout
    if let Err(e) = write_stdout(&pipeline_data) {
        CompilerError::new(
            "transform-actions",
            "OUTPUT_ERROR",
            format!("Failed to write output: {}", e)
        ).exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use serde_json::json;
    use common::{Metadata, Token, Protocol, Chain, Action, Rational};

    #[test]
    fn test_full_transformation() {
        let input = PipelineData {
            metadata: Metadata {
                opportunity_id: "test123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: Some(vec![
                json!({
                    "action": "borrow",
                    "amount": "100.5",
                    "token": "WETH",
                    "protocol": "aave"
                }),
                json!({
                    "action": "bridge",
                    "to": "arbitrum",
                    "token": "WETH",
                    "amount": "100.5"
                }),
                json!({
                    "action": "swap",
                    "amount": "100.5",
                    "from": "WETH",
                    "to": "USDC",
                    "minOut": "150000",
                    "protocol": "uniswapv2"
                }),
                json!({
                    "action": "bridge",
                    "to": "polygon",
                    "token": "USDC", 
                    "amount": "150000"
                }),
                json!({
                    "action": "repay",
                    "amount": "100.5",
                    "token": "WETH",
                    "protocol": "aave"
                }),
            ]),
            typed_actions: None,
            expr: None,
            constraints: json!({}),
        };

        // Serialize and process
        let input_json = serde_json::to_string(&input).unwrap();
        // In real execution, this would go through the main function
        
        // Manually test the transformation
        let actions = input.actions.unwrap();
        let mut typed_actions = Vec::new();

        for (index, action) in actions.iter().enumerate() {
            let normalized = normalizer::normalize_amounts(action, index).unwrap();
            let typed = mapper::map_to_typed(&normalized, index).unwrap();
            typed_actions.push(typed);
        }

        let with_chains = chain_tracker::infer_chains(typed_actions, Some("polygon")).unwrap();

        // Verify transformations
        assert_eq!(with_chains.len(), 5);
        
        // First action: borrow on polygon
        match &with_chains[0].action {
            Action::Borrow { amount, token, protocol } => {
                assert_eq!(amount.num, 201); // 100.5 = 201/2
                assert_eq!(amount.den, 2);
                assert_eq!(*token, Token::WETH);
                assert_eq!(*protocol, Protocol::Aave);
            },
            _ => panic!("Expected Borrow action"),
        }
        assert_eq!(with_chains[0].chain, Some(Chain::Polygon));

        // Second action: bridge from polygon
        match &with_chains[1].action {
            Action::Bridge { chain, token, amount } => {
                assert_eq!(*chain, Chain::Arbitrum);
                assert_eq!(*token, Token::WETH);
                assert_eq!(amount.num, 201);
                assert_eq!(amount.den, 2);
            },
            _ => panic!("Expected Bridge action"),
        }
        assert_eq!(with_chains[1].chain, Some(Chain::Polygon));

        // Third action: swap on arbitrum  
        match &with_chains[2].action {
            Action::Swap { amount_in, token_in, token_out, min_out, protocol } => {
                assert_eq!(amount_in.num, 201);
                assert_eq!(amount_in.den, 2);
                assert_eq!(*token_in, Token::WETH);
                assert_eq!(*token_out, Token::USDC);
                assert_eq!(min_out.num, 150000);
                assert_eq!(*protocol, Protocol::UniswapV2);
            },
            _ => panic!("Expected Swap action"),
        }
        assert_eq!(with_chains[2].chain, Some(Chain::Arbitrum));

        // Fourth action: bridge back to polygon
        match &with_chains[3].action {
            Action::Bridge { chain, token, amount } => {
                assert_eq!(*chain, Chain::Polygon);
                assert_eq!(*token, Token::USDC);
                assert_eq!(amount.num, 150000);
                assert_eq!(amount.den, 1);
            },
            _ => panic!("Expected Bridge action"),
        }
        assert_eq!(with_chains[3].chain, Some(Chain::Arbitrum));

        // Fifth action: repay on polygon
        match &with_chains[4].action {
            Action::Repay { amount, token, protocol } => {
                assert_eq!(amount.num, 201); // 100.5 = 201/2
                assert_eq!(amount.den, 2);
                assert_eq!(*token, Token::WETH);
                assert_eq!(*protocol, Protocol::Aave);
            },
            _ => panic!("Expected Repay action"),
        }
        assert_eq!(with_chains[4].chain, Some(Chain::Polygon));
    }

    #[test]
    fn test_custom_tokens_and_protocols() {
        let input = PipelineData {
            metadata: Metadata {
                opportunity_id: "test123".to_string(),
                source_chain: None,
                target_chain: None,
                timestamp: None,
                expected_profit: None,
                confidence: None,
            },
            actions: Some(vec![
                json!({
                    "action": "swap",
                    "amount": "1000",
                    "from": "LINK",
                    "to": "custom:MKR",
                    "minOut": "50",
                    "protocol": "curve"
                }),
            ]),
            typed_actions: None,
            expr: None,
            constraints: json!({}),
        };

        let actions = input.actions.unwrap();
        let normalized = normalizer::normalize_amounts(&actions[0], 0).unwrap();
        let typed = mapper::map_to_typed(&normalized, 0).unwrap();

        match &typed.action {
            Action::Swap { token_in, token_out, protocol, .. } => {
                assert_eq!(*token_in, Token::Custom("LINK".to_string()));
                assert_eq!(*token_out, Token::Custom("MKR".to_string()));
                assert_eq!(*protocol, Protocol::Custom("curve".to_string()));
            },
            _ => panic!("Expected Swap action"),
        }
    }
}