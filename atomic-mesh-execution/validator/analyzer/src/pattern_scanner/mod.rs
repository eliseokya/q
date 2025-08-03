//! Pattern scanner module for extracting theorems from Lean files

pub mod lean_parser;
pub mod theorem_database;

pub use lean_parser::LeanParser;
pub use theorem_database::{TheoremDatabase, Theorem};