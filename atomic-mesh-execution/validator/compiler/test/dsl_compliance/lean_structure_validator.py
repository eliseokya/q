#!/usr/bin/env python3
"""
Lean DSL Structure Validator

Validates that compiler output exactly matches the structure defined
in maths/DSL/Syntax.lean
"""

import json
import sys
from typing import Dict, Any, List

def validate_token(token: Any) -> bool:
    """Validate token matches Lean DSL Token type"""
    if isinstance(token, str):
        valid_tokens = ["ETH", "WETH", "USDC", "DAI", "WBTC"]
        return token in valid_tokens or token.startswith("0x")  # custom token
    return False

def validate_protocol(protocol: Any) -> bool:
    """Validate protocol matches Lean DSL Protocol type"""
    if isinstance(protocol, str):
        valid_protocols = ["Aave", "UniswapV2", "Compound"]
        return protocol in valid_protocols or "-" in protocol  # custom protocol
    return False

def validate_chain(chain: Any) -> bool:
    """Validate chain matches Lean DSL Chain type"""
    return chain in ["polygon", "arbitrum"]

def validate_rational(amount: Any) -> bool:
    """Validate rational number structure"""
    if isinstance(amount, dict):
        return "num" in amount and "den" in amount and \
               isinstance(amount["num"], int) and isinstance(amount["den"], int)
    return False

def validate_action(action: Dict[str, Any]) -> bool:
    """Validate action matches Lean DSL Action type"""
    if not isinstance(action, dict) or "type" not in action:
        return False
    
    action_type = action["type"]
    
    if action_type in ["borrow", "repay"]:
        return (validate_rational(action.get("amount")) and
                validate_token(action.get("token")) and
                validate_protocol(action.get("protocol")))
    
    elif action_type == "swap":
        return (validate_rational(action.get("amount_in")) and
                validate_token(action.get("token_in")) and
                validate_token(action.get("token_out")) and
                validate_rational(action.get("min_out")) and
                validate_protocol(action.get("protocol")))
    
    elif action_type in ["deposit", "withdraw"]:
        return (validate_rational(action.get("amount")) and
                validate_token(action.get("token")) and
                validate_protocol(action.get("protocol")))
    
    elif action_type == "bridge":
        return (validate_chain(action.get("chain")) and
                validate_token(action.get("token")) and
                validate_rational(action.get("amount")))
    
    return False

def validate_constraint(constraint: Dict[str, Any]) -> bool:
    """Validate constraint matches Lean DSL Constraint type"""
    if not isinstance(constraint, dict) or "type" not in constraint:
        return False
    
    constraint_type = constraint["type"]
    
    if constraint_type == "deadline":
        return isinstance(constraint.get("blocks"), int)
    elif constraint_type == "maxGas":
        return isinstance(constraint.get("amount"), int)
    elif constraint_type == "minBalance":
        return (validate_token(constraint.get("token")) and
                validate_rational(constraint.get("amount")))
    elif constraint_type == "invariant":
        return isinstance(constraint.get("name"), str)
    
    return False

def validate_expr(expr: Dict[str, Any]) -> bool:
    """Validate expression matches Lean DSL Expr type"""
    if not isinstance(expr, dict) or "type" not in expr:
        return False
    
    expr_type = expr["type"]
    
    if expr_type == "action":
        return validate_action(expr.get("action", {}))
    
    elif expr_type == "seq":
        return (validate_expr(expr.get("e1", {})) and
                validate_expr(expr.get("e2", {})))
    
    elif expr_type == "parallel":
        exprs = expr.get("exprs", [])
        return isinstance(exprs, list) and all(validate_expr(e) for e in exprs)
    
    elif expr_type == "onChain":
        return (validate_chain(expr.get("chain")) and
                validate_expr(expr.get("expr", {})))
    
    return False

def validate_bundle(bundle: Dict[str, Any]) -> List[str]:
    """Validate complete bundle structure"""
    errors = []
    
    # Check required fields
    required_fields = ["name", "startChain", "expr", "constraints"]
    for field in required_fields:
        if field not in bundle:
            errors.append(f"Missing required field: {field}")
    
    # Validate name
    if not isinstance(bundle.get("name"), str):
        errors.append("Bundle name must be string")
    
    # Validate startChain
    if not validate_chain(bundle.get("startChain")):
        errors.append(f"Invalid startChain: {bundle.get('startChain')}")
    
    # Validate expression
    if not validate_expr(bundle.get("expr", {})):
        errors.append("Invalid expression structure")
    
    # Validate constraints
    constraints = bundle.get("constraints", [])
    if not isinstance(constraints, list):
        errors.append("Constraints must be a list")
    else:
        for i, constraint in enumerate(constraints):
            if not validate_constraint(constraint):
                errors.append(f"Invalid constraint at index {i}")
    
    return errors

def main():
    if len(sys.argv) != 2:
        print("Usage: python3 lean_structure_validator.py <bundle.json>")
        sys.exit(1)
    
    try:
        with open(sys.argv[1], 'r') as f:
            bundle = json.load(f)
        
        errors = validate_bundle(bundle)
        
        if errors:
            print("❌ DSL Structure Validation FAILED:")
            for error in errors:
                print(f"  • {error}")
            sys.exit(1)
        else:
            print("✅ DSL Structure Validation PASSED")
            print("   Bundle structure perfectly matches Lean DSL specification")
            sys.exit(0)
    
    except FileNotFoundError:
        print(f"❌ File not found: {sys.argv[1]}")
        sys.exit(1)
    except json.JSONDecodeError as e:
        print(f"❌ Invalid JSON: {e}")
        sys.exit(1)
    except Exception as e:
        print(f"❌ Validation error: {e}")
        sys.exit(1)

if __name__ == "__main__":
    main()