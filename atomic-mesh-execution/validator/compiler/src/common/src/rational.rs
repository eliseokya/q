//! Rational number implementation with exact arithmetic

use crate::types::Rational;
use std::str::FromStr;

impl Rational {
    /// Create a new rational number, automatically reducing to lowest terms
    pub fn new_reduced(num: u64, den: u64) -> Self {
        if den == 0 {
            panic!("Denominator cannot be zero");
        }
        let gcd = gcd(num, den);
        Self {
            num: num / gcd,
            den: den / gcd,
        }
    }

    /// Parse a decimal string into a rational number
    pub fn from_decimal_str(s: &str) -> Result<Self, String> {
        // Handle scientific notation
        if s.contains('e') || s.contains('E') {
            return Self::from_scientific_notation(s);
        }

        // Handle regular decimal
        if let Some(dot_pos) = s.find('.') {
            let whole = &s[..dot_pos];
            let fractional = &s[dot_pos + 1..];
            
            // Validate parts
            if whole.is_empty() && fractional.is_empty() {
                return Err("Invalid decimal: missing digits".to_string());
            }

            let whole_num = if whole.is_empty() {
                0
            } else {
                whole.parse::<u64>()
                    .map_err(|_| format!("Invalid whole number: {}", whole))?
            };

            let fractional_num = if fractional.is_empty() {
                0
            } else {
                fractional.parse::<u64>()
                    .map_err(|_| format!("Invalid fractional part: {}", fractional))?
            };

            let decimal_places = fractional.len();
            let denominator = 10u64.pow(decimal_places as u32);
            let numerator = whole_num * denominator + fractional_num;

            Ok(Self::new_reduced(numerator, denominator))
        } else {
            // Just an integer
            let num = s.parse::<u64>()
                .map_err(|_| format!("Invalid integer: {}", s))?;
            Ok(Self::from_integer(num))
        }
    }

    /// Parse scientific notation
    fn from_scientific_notation(s: &str) -> Result<Self, String> {
        let parts: Vec<&str> = s.split(|c| c == 'e' || c == 'E').collect();
        if parts.len() != 2 {
            return Err("Invalid scientific notation".to_string());
        }

        let base = Self::from_decimal_str(parts[0])?;
        let exponent = parts[1].parse::<i32>()
            .map_err(|_| "Invalid exponent".to_string())?;

        if exponent >= 0 {
            let multiplier = 10u64.pow(exponent as u32);
            Ok(Self::new_reduced(base.num * multiplier, base.den))
        } else {
            let divisor = 10u64.pow((-exponent) as u32);
            Ok(Self::new_reduced(base.num, base.den * divisor))
        }
    }

    /// Convert to decimal string representation
    pub fn to_decimal_string(&self) -> String {
        if self.den == 1 {
            self.num.to_string()
        } else {
            let whole = self.num / self.den;
            let remainder = self.num % self.den;
            if remainder == 0 {
                whole.to_string()
            } else {
                format!("{}.{}", whole, (remainder as f64 / self.den as f64).to_string().trim_start_matches("0."))
            }
        }
    }

    /// Add two rational numbers
    pub fn add(&self, other: &Self) -> Self {
        let num = self.num * other.den + other.num * self.den;
        let den = self.den * other.den;
        Self::new_reduced(num, den)
    }

    /// Multiply two rational numbers
    pub fn mul(&self, other: &Self) -> Self {
        let num = self.num * other.num;
        let den = self.den * other.den;
        Self::new_reduced(num, den)
    }

    /// Check if this rational is less than another
    pub fn lt(&self, other: &Self) -> bool {
        self.num * other.den < other.num * self.den
    }
}

/// Calculate greatest common divisor using Euclid's algorithm
fn gcd(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let temp = b;
        b = a % b;
        a = temp;
    }
    a
}

impl FromStr for Rational {
    type Err = String;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        Self::from_decimal_str(s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_from_integer() {
        let r = Rational::from_integer(100);
        assert_eq!(r.num, 100);
        assert_eq!(r.den, 1);
    }

    #[test]
    fn test_from_decimal() {
        let r = Rational::from_decimal_str("1.5").unwrap();
        assert_eq!(r.num, 3);
        assert_eq!(r.den, 2);

        let r = Rational::from_decimal_str("0.1").unwrap();
        assert_eq!(r.num, 1);
        assert_eq!(r.den, 10);

        let r = Rational::from_decimal_str("123.456").unwrap();
        assert_eq!(r.num, 15432);
        assert_eq!(r.den, 125);
    }

    #[test]
    fn test_scientific_notation() {
        let r = Rational::from_decimal_str("1e18").unwrap();
        assert_eq!(r.num, 1_000_000_000_000_000_000);
        assert_eq!(r.den, 1);

        let r = Rational::from_decimal_str("1.5e2").unwrap();
        assert_eq!(r.num, 150);
        assert_eq!(r.den, 1);
    }

    #[test]
    fn test_reduction() {
        let r = Rational::new_reduced(50, 100);
        assert_eq!(r.num, 1);
        assert_eq!(r.den, 2);
    }
}