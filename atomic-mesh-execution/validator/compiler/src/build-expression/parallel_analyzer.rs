//! Analyze opportunities for parallel execution

use common::{TypedAction, Action, Token, Protocol, Chain, CompilerError, build_errors};
use serde_json::json;
use std::collections::{HashSet, HashMap};

/// Represents a group of actions that can execute in parallel
#[derive(Debug, Clone)]
pub struct ParallelGroup {
    pub start_index: usize,
    pub end_index: usize, // Inclusive
    pub actions: Vec<usize>, // Indices of actions in this group
}

/// Analyze actions for parallel execution opportunities
pub fn analyze_parallel_opportunities(
    actions: &[TypedAction]
) -> Result<Vec<ParallelGroup>, CompilerError> {
    if actions.len() < 2 {
        // No parallelization possible with 0 or 1 action
        return Ok(vec![]);
    }

    let mut parallel_groups = Vec::new();
    let mut processed = vec![false; actions.len()];

    for i in 0..actions.len() {
        if processed[i] {
            continue;
        }

        // Try to build a parallel group starting from this action
        let mut group_actions = vec![i];
        processed[i] = true;

        // Look for actions that can be parallelized with this one
        for j in (i + 1)..actions.len() {
            if processed[j] {
                continue;
            }

            // Check if action j can be parallelized with all actions in the group
            let can_add = group_actions.iter().all(|&k| {
                can_parallelize(&actions[k], &actions[j])
            });

            if can_add {
                // Additional check: ensure all actions in group are on same chain
                if !same_chain_context(&actions[i], &actions[j]) {
                    break; // Can't parallelize across chains
                }
                
                group_actions.push(j);
                processed[j] = true;
            }
        }

        // Only create a group if we found at least 2 actions
        if group_actions.len() >= 2 {
            parallel_groups.push(ParallelGroup {
                start_index: *group_actions.first().unwrap(),
                end_index: *group_actions.last().unwrap(),
                actions: group_actions,
            });
        }
    }

    Ok(parallel_groups)
}

/// Check if two actions can be executed in parallel
fn can_parallelize(action1: &TypedAction, action2: &TypedAction) -> bool {
    // Rule 1: Actions must be on the same chain
    if !same_chain_context(action1, action2) {
        return false;
    }

    // Rule 2: No data dependencies
    if has_data_dependency(action1, action2) {
        return false;
    }

    // Rule 3: No atomicity conflicts
    if has_atomicity_conflict(action1, action2) {
        return false;
    }

    // Rule 4: No protocol conflicts
    if has_protocol_conflict(action1, action2) {
        return false;
    }

    true
}

/// Check if actions are on the same chain
fn same_chain_context(action1: &TypedAction, action2: &TypedAction) -> bool {
    action1.chain == action2.chain
}

/// Check for data dependencies between actions
fn has_data_dependency(action1: &TypedAction, action2: &TypedAction) -> bool {
    // Extract tokens involved in each action
    let tokens1 = get_involved_tokens(&action1.action);
    let tokens2 = get_involved_tokens(&action2.action);

    // Check for token conflicts
    for (token1, is_output1) in &tokens1 {
        for (token2, is_output2) in &tokens2 {
            if token1 == token2 {
                // If one produces and the other consumes the same token, there's a dependency
                if *is_output1 && !*is_output2 {
                    return true; // action1 produces token that action2 needs
                }
                if !*is_output1 && *is_output2 {
                    return true; // action2 produces token that action1 needs
                }
                // If both consume or both produce, allow parallel execution
                // (we assume sufficient balance for multiple consumers)
                // and multiple producers of the same token can coexist
            }
        }
    }

    false
}

/// Get tokens involved in an action (token, is_output)
fn get_involved_tokens(action: &Action) -> Vec<(Token, bool)> {
    match action {
        Action::Borrow { token, .. } => vec![(token.clone(), true)], // Produces token
        Action::Repay { token, .. } => vec![(token.clone(), false)], // Consumes token
        Action::Deposit { token, .. } => vec![(token.clone(), false)], // Consumes token
        Action::Withdraw { token, .. } => vec![(token.clone(), true)], // Produces token
        Action::Swap { token_in, token_out, .. } => {
            vec![(token_in.clone(), false), (token_out.clone(), true)]
        },
        Action::Bridge { token, .. } => vec![(token.clone(), false)], // Consumes on source
    }
}

/// Check for atomicity conflicts
fn has_atomicity_conflict(action1: &TypedAction, action2: &TypedAction) -> bool {
    // Bridges cannot be parallelized as they change chain context
    matches!(&action1.action, Action::Bridge { .. }) || 
    matches!(&action2.action, Action::Bridge { .. })
}

/// Check for protocol conflicts
fn has_protocol_conflict(action1: &TypedAction, action2: &TypedAction) -> bool {
    // Extract protocols
    let protocol1 = get_protocol(&action1.action);
    let protocol2 = get_protocol(&action2.action);

    match (protocol1, protocol2) {
        (Some(p1), Some(p2)) if p1 == p2 => {
            // Same protocol - check if operations conflict
            match (&action1.action, &action2.action) {
                // Borrow and repay on same protocol conflict
                (Action::Borrow { .. }, Action::Repay { .. }) |
                (Action::Repay { .. }, Action::Borrow { .. }) => true,
                
                // Deposit and withdraw on same protocol conflict
                (Action::Deposit { .. }, Action::Withdraw { .. }) |
                (Action::Withdraw { .. }, Action::Deposit { .. }) => true,
                
                // Multiple borrows from same protocol might hit limits
                (Action::Borrow { .. }, Action::Borrow { .. }) => true,
                
                _ => false,
            }
        },
        _ => false,
    }
}

/// Extract protocol from action
fn get_protocol(action: &Action) -> Option<&Protocol> {
    match action {
        Action::Borrow { protocol, .. } |
        Action::Repay { protocol, .. } |
        Action::Deposit { protocol, .. } |
        Action::Withdraw { protocol, .. } |
        Action::Swap { protocol, .. } => Some(protocol),
        Action::Bridge { .. } => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use common::{Rational, Token, Protocol, Chain};

    fn create_borrow(token: Token, protocol: Protocol, chain: Chain) -> TypedAction {
        TypedAction {
            action: Action::Borrow {
                amount: Rational::from_integer(100),
                token,
                protocol,
            },
            chain: Some(chain),
        }
    }

    fn create_swap(from: Token, to: Token, protocol: Protocol, chain: Chain) -> TypedAction {
        TypedAction {
            action: Action::Swap {
                amount_in: Rational::from_integer(100),
                token_in: from,
                token_out: to,
                min_out: Rational::from_integer(0),
                protocol,
            },
            chain: Some(chain),
        }
    }

    #[test]
    fn test_parallel_swaps_different_tokens() {
        let actions = vec![
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::DAI, Token::WBTC, Protocol::UniswapV2, Chain::Polygon),
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].actions.len(), 2);
    }

    #[test]
    fn test_no_parallel_data_dependency() {
        let actions = vec![
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::USDC, Token::DAI, Protocol::UniswapV2, Chain::Polygon),
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 0); // Can't parallelize due to USDC dependency
    }

    #[test]
    fn test_no_parallel_different_chains() {
        let actions = vec![
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::DAI, Token::WBTC, Protocol::UniswapV2, Chain::Arbitrum),
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 0); // Can't parallelize across chains
    }

    #[test]
    fn test_no_parallel_with_bridge() {
        let actions = vec![
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            TypedAction {
                action: Action::Bridge {
                    chain: Chain::Arbitrum,
                    token: Token::USDC,
                    amount: Rational::from_integer(100),
                },
                chain: Some(Chain::Polygon),
            },
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 0); // Bridges can't be parallelized
    }

    #[test]
    fn test_no_parallel_protocol_conflict() {
        let actions = vec![
            create_borrow(Token::WETH, Protocol::Aave, Chain::Polygon),
            TypedAction {
                action: Action::Repay {
                    amount: Rational::from_integer(100),
                    token: Token::WETH,
                    protocol: Protocol::Aave,
                },
                chain: Some(Chain::Polygon),
            },
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 0); // Borrow/Repay on same protocol conflict
    }

    #[test]
    fn test_multiple_parallel_groups() {
        let actions = vec![
            // Group 1: Two independent swaps
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::DAI, Token::WBTC, Protocol::UniswapV2, Chain::Polygon),
            // Can't parallelize with above due to USDC dependency
            create_swap(Token::USDC, Token::DAI, Protocol::Compound, Chain::Polygon),
            // Group 2: Two more independent swaps
            create_swap(Token::Custom("LINK".to_string()), Token::Custom("AAVE".to_string()), 
                       Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::Custom("UNI".to_string()), Token::Custom("SUSHI".to_string()), 
                       Protocol::UniswapV2, Chain::Polygon),
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 2);
        assert_eq!(groups[0].actions, vec![0, 1]);
        assert_eq!(groups[1].actions, vec![3, 4]);
    }

    #[test]
    fn test_three_way_parallel() {
        let actions = vec![
            create_swap(Token::WETH, Token::USDC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::DAI, Token::WBTC, Protocol::UniswapV2, Chain::Polygon),
            create_swap(Token::Custom("LINK".to_string()), Token::Custom("AAVE".to_string()), 
                       Protocol::Compound, Chain::Polygon),
        ];

        let groups = analyze_parallel_opportunities(&actions).unwrap();
        assert_eq!(groups.len(), 1);
        assert_eq!(groups[0].actions.len(), 3);
    }
}