//! Performance budget enforcement for analyzer operations
//!
//! This module defines performance budgets and provides enforcement mechanisms
//! to ensure the analyzer meets its timing requirements.

use thiserror::Error;

#[derive(Error, Debug)]
pub enum BudgetError {
    #[error("Total analysis time {actual}μs exceeded budget {budget}μs")]
    TotalBudgetExceeded { budget: u64, actual: u64 },
    
    #[error("Operation {operation} took {actual}μs, exceeding budget {budget}μs")]
    OperationBudgetExceeded {
        operation: String,
        budget: u64,
        actual: u64,
    },
}

/// Performance budget for analyzer operations
#[derive(Debug, Clone)]
pub struct PerformanceBudget {
    /// Total budget for complete analysis (target: 500μs)
    pub total_budget_us: u64,
    /// Budget for input parsing
    pub input_parsing_us: u64,
    /// Budget for pattern loading
    pub pattern_loading_us: u64,
    /// Budget for structural matching
    pub structural_matching_us: u64,
    /// Budget for constraint validation
    pub constraint_validation_us: u64,
    /// Budget for semantic validation
    pub semantic_validation_us: u64,
    /// Budget for result formatting
    pub result_formatting_us: u64,
}

impl PerformanceBudget {
    /// Create default performance budget (500μs total)
    pub fn default_budget() -> Self {
        Self {
            total_budget_us: 500,        // Total target
            input_parsing_us: 50,        // JSON parsing
            pattern_loading_us: 20,      // Pattern library access
            structural_matching_us: 200, // Main pattern matching
            constraint_validation_us: 100, // Constraint checks
            semantic_validation_us: 80,  // Theorem application
            result_formatting_us: 50,    // Output generation
        }
    }

    /// Create a relaxed budget for development (2ms total)
    pub fn development_budget() -> Self {
        Self {
            total_budget_us: 2000,       // 2ms for development
            input_parsing_us: 200,       // More lenient
            pattern_loading_us: 100,     
            structural_matching_us: 800, 
            constraint_validation_us: 400,
            semantic_validation_us: 300,
            result_formatting_us: 200,
        }
    }

    /// Create a strict budget for production (300μs total)
    pub fn strict_budget() -> Self {
        Self {
            total_budget_us: 300,        // Aggressive target
            input_parsing_us: 30,        
            pattern_loading_us: 10,      
            structural_matching_us: 120, 
            constraint_validation_us: 60,
            semantic_validation_us: 50,
            result_formatting_us: 30,
        }
    }
}

impl Default for PerformanceBudget {
    fn default() -> Self {
        Self::default_budget()
    }
}

/// Enforces performance budgets during analysis
pub struct BudgetEnforcer {
    budget: PerformanceBudget,
    strict_mode: bool,
}

impl BudgetEnforcer {
    /// Create a new budget enforcer
    pub fn new(budget: PerformanceBudget) -> Self {
        Self {
            budget,
            strict_mode: false,
        }
    }

    /// Create enforcer with default budget
    pub fn default() -> Self {
        Self::new(PerformanceBudget::default())
    }

    /// Enable strict mode (fail fast on budget violations)
    pub fn with_strict_mode(mut self) -> Self {
        self.strict_mode = true;
        self
    }

    /// Check if operation timing is within budget
    pub fn check_operation(&self, operation: &str, duration_us: u64) -> Result<(), BudgetError> {
        let budget = match operation {
            "input_parsing" => self.budget.input_parsing_us,
            "pattern_loading" => self.budget.pattern_loading_us,
            "structural_matching" => self.budget.structural_matching_us,
            "constraint_validation" => self.budget.constraint_validation_us,
            "semantic_validation" => self.budget.semantic_validation_us,
            "result_formatting" => self.budget.result_formatting_us,
            _ => return Ok(()), // Unknown operations are not checked
        };

        if duration_us > budget {
            let error = BudgetError::OperationBudgetExceeded {
                operation: operation.to_string(),
                budget,
                actual: duration_us,
            };
            
            if self.strict_mode {
                return Err(error);
            } else {
                // In non-strict mode, just log the violation
                log::warn!("Performance budget violation: {}", error);
            }
        }

        Ok(())
    }

    /// Check if total timing is within budget
    pub fn check_total(&self, total_us: u64) -> Result<(), BudgetError> {
        if total_us > self.budget.total_budget_us {
            let error = BudgetError::TotalBudgetExceeded {
                budget: self.budget.total_budget_us,
                actual: total_us,
            };
            
            if self.strict_mode {
                return Err(error);
            } else {
                log::warn!("Total performance budget violation: {}", error);
            }
        }

        Ok(())
    }

    /// Get the current budget
    pub fn budget(&self) -> &PerformanceBudget {
        &self.budget
    }

    /// Update the budget
    pub fn set_budget(&mut self, budget: PerformanceBudget) {
        self.budget = budget;
    }

    /// Check if enforcer is in strict mode
    pub fn is_strict(&self) -> bool {
        self.strict_mode
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_default_budget() {
        let budget = PerformanceBudget::default();
        assert_eq!(budget.total_budget_us, 500);
        assert_eq!(budget.input_parsing_us, 50);
        assert_eq!(budget.structural_matching_us, 200);
    }

    #[test]
    fn test_development_budget() {
        let budget = PerformanceBudget::development_budget();
        assert_eq!(budget.total_budget_us, 2000);
        assert!(budget.input_parsing_us > PerformanceBudget::default().input_parsing_us);
    }

    #[test]
    fn test_budget_enforcer() {
        let enforcer = BudgetEnforcer::default();
        
        // Within budget should be OK
        assert!(enforcer.check_operation("input_parsing", 40).is_ok());
        assert!(enforcer.check_total(400).is_ok());
        
        // Exceeding budget in non-strict mode logs warning but doesn't error
        assert!(enforcer.check_operation("input_parsing", 60).is_ok());
        assert!(enforcer.check_total(600).is_ok());
    }

    #[test]
    fn test_strict_mode() {
        let enforcer = BudgetEnforcer::default().with_strict_mode();
        
        // Within budget is still OK
        assert!(enforcer.check_operation("input_parsing", 40).is_ok());
        
        // Exceeding budget in strict mode returns error
        assert!(enforcer.check_operation("input_parsing", 60).is_err());
        assert!(enforcer.check_total(600).is_err());
    }
}