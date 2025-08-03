//! Assemble bundle component - Fourth and final stage of the compiler pipeline
//! Creates the final DSL Bundle structure

mod assembler;

use common::{
    CompilerError,
    errors::{read_stdin, write_stdout},
};

fn main() {
    // Read input from stdin
    let input = match read_stdin() {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "assemble-bundle",
                "IO_ERROR",
                format!("Failed to read input: {}", e)
            ).exit(1);
        }
    };

    // Parse pipeline data
    let pipeline_data = match serde_json::from_str(&input) {
        Ok(data) => data,
        Err(e) => {
            CompilerError::new(
                "assemble-bundle",
                "PARSE_ERROR",
                format!("Failed to parse pipeline data: {}", e)
            ).exit(1);
        }
    };

    // Assemble the bundle
    let bundle = match assembler::assemble_bundle(pipeline_data) {
        Ok(bundle) => bundle,
        Err(e) => e.exit(2),
    };

    // Write output to stdout
    if let Err(e) = write_stdout(&bundle) {
        CompilerError::new(
            "assemble-bundle",
            "OUTPUT_ERROR",
            format!("Failed to write output: {}", e)
        ).exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{
        PipelineData, Metadata, Expr, Action, Token, Protocol, 
        Chain, Rational, Bundle, Constraint
    };
    use serde_json::json;

    #[test]
    fn test_complete_assembly() {
        let pipeline_data = PipelineData {
            metadata: Metadata {
                opportunity_id: "flash-loan-123".to_string(),
                source_chain: Some("polygon".to_string()),
                target_chain: Some("polygon".to_string()),
                timestamp: Some("2024-01-01T00:00:00Z".to_string()),
                expected_profit: Some("500".to_string()),
                confidence: Some(0.95),
            },
            actions: None,
            typed_actions: None,
            expr: Some(Expr::OnChain {
                chain: Chain::Polygon,
                expr: Box::new(Expr::Seq {
                    e1: Box::new(Expr::Action { action: Action::Borrow {
                        amount: Rational::from_integer(1000),
                        token: Token::WETH,
                        protocol: Protocol::Aave,
                    } }),
                    e2: Box::new(Expr::Seq {
                        e1: Box::new(Expr::Action { action: Action::Swap {
                            amount_in: Rational::from_integer(1000),
                            token_in: Token::WETH,
                            token_out: Token::USDC,
                            min_out: Rational::from_integer(1500000),
                            protocol: Protocol::UniswapV2,
                        } }),
                        e2: Box::new(Expr::Action { action: Action::Repay {
                            amount: Rational::from_integer(1000),
                            token: Token::WETH,
                            protocol: Protocol::Aave,
                        } })
                    })
                })
            }),
            constraints: json!({
                "deadline": 20,
                "max_gas": 500000,
                "min_balance": {
                    "token": "USDC",
                    "amount": "100"
                },
                "invariants": ["constant-product"]
            }),
        };

        // Process through assembler
        let bundle = assembler::assemble_bundle(pipeline_data).unwrap();

        // Verify bundle structure
        assert_eq!(bundle.name, "bundle-flash-loan-123");
        assert_eq!(bundle.start_chain, Chain::Polygon);
        
        // Check expression structure
        match &bundle.expr {
            Expr::OnChain { chain, expr: inner } => {
                assert_eq!(*chain, Chain::Polygon);
                assert!(matches!(&**inner, Expr::Seq { e1: _, e2: _ }));
            },
            _ => panic!("Expected OnChain wrapper"),
        }

        // Check constraints
        assert_eq!(bundle.constraints.len(), 4);
        assert!(bundle.constraints.iter().any(|c| matches!(c, Constraint::Deadline { blocks: _ })));
        assert!(bundle.constraints.iter().any(|c| matches!(c, Constraint::MaxGas { amount: _ })));
        assert!(bundle.constraints.iter().any(|c| matches!(c, Constraint::MinBalance { token: _, amount: _ })));
        assert!(bundle.constraints.iter().any(|c| matches!(c, Constraint::Invariant { name: _ })));
    }

    #[test]
    fn test_json_serialization() {
        let bundle = Bundle {
            name: "test-bundle".to_string(),
            start_chain: Chain::Polygon,
            expr: Expr::Action { action: Action::Borrow {
                amount: Rational { num: 100, den: 1 },
                token: Token::WETH,
                protocol: Protocol::Aave,
            } },
            constraints: vec![
                Constraint::Deadline { blocks: 30 },
                Constraint::MaxGas { amount: 1000000 },
            ],
        };

        // Serialize to JSON
        let json = serde_json::to_value(&bundle).unwrap();
        
        // Verify JSON structure
        assert_eq!(json["name"], "test-bundle");
        assert_eq!(json["start_chain"], "polygon");
        assert!(json["expr"].is_object());
        assert!(json["constraints"].is_array());
        assert_eq!(json["constraints"].as_array().unwrap().len(), 2);
    }
}