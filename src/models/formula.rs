use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::sync::Arc;

/// Type alias for shared ownership of formulas using Arc
/// Use this when you need to share formulas across multiple owners without cloning
pub type SharedFormula = Arc<Formula>;

/// A step in a path through the formula AST.
/// Paths identify a specific node by position, not by structural equality.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum PathStep {
    /// Go into the inner formula of a Not
    Inner,
    /// Go into the left child of a binary connective
    Left,
    /// Go into the right child of a binary connective
    Right,
}

/// Represents a propositional logic formula
#[derive(Debug, Clone, PartialEq, Eq, Hash, Serialize, Deserialize)]
#[serde(tag = "type", content = "value")]
pub enum Formula {
    Atom(String),
    Not(Box<Formula>),
    And(Box<Formula>, Box<Formula>),
    Or(Box<Formula>, Box<Formula>),
    Implies(Box<Formula>, Box<Formula>),
    Biconditional(Box<Formula>, Box<Formula>),
    Contradiction,
}

impl Formula {
    /// Wrap formula in Arc for shared ownership
    /// Use this when you need to share a formula across multiple owners without cloning
    pub fn shared(self) -> SharedFormula {
        Arc::new(self)
    }

    /// Clone from Arc reference
    /// Use this when you need an owned copy from a SharedFormula
    pub fn from_shared(shared: &SharedFormula) -> Formula {
        (**shared).clone()
    }

    /// Display string using logical symbols (⊃, ∨, ., ≡, ~, ⊥)
    /// Uses bracket hierarchy: innermost () → [] → {} outermost
    pub fn display_string(&self) -> String {
        let max_depth = self.bracket_depth();
        self.display_with_depth(0, max_depth)
    }

    /// Calculate maximum bracket nesting depth needed
    fn bracket_depth(&self) -> usize {
        match self {
            Formula::Atom(_) | Formula::Contradiction => 0,
            Formula::Not(inner) => {
                if inner.needs_parens_for_not() {
                    1 + inner.bracket_depth()
                } else {
                    inner.bracket_depth()
                }
            }
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right)
            | Formula::Biconditional(left, right) => {
                let left_needs = Self::subformula_bracket_depth(left);
                let right_needs = Self::subformula_bracket_depth(right);
                left_needs.max(right_needs)
            }
        }
    }

    fn subformula_bracket_depth(formula: &Formula) -> usize {
        match formula {
            Formula::Atom(_) | Formula::Contradiction => 0,
            Formula::Not(inner) if matches!(inner.as_ref(), Formula::Atom(_)) => 0,
            _ => 1 + formula.bracket_depth(),
        }
    }

    fn display_with_depth(&self, current_depth: usize, max_depth: usize) -> String {
        match self {
            Formula::Atom(name) => name.clone(),
            Formula::Not(inner) => {
                if inner.needs_parens_for_not() {
                    let inner_str = inner.display_with_depth(current_depth + 1, max_depth);
                    let (open, close) = Self::brackets_for_level(current_depth, max_depth);
                    format!("~{}{}{}", open, inner_str, close)
                } else {
                    let inner_str = inner.display_with_depth(current_depth, max_depth);
                    format!("~{}", inner_str)
                }
            }
            Formula::And(left, right) => {
                let left_str = Self::wrap_if_compound(left, current_depth, max_depth);
                let right_str = Self::wrap_if_compound(right, current_depth, max_depth);
                format!("{} . {}", left_str, right_str)
            }
            Formula::Or(left, right) => {
                let left_str = Self::wrap_if_compound(left, current_depth, max_depth);
                let right_str = Self::wrap_if_compound(right, current_depth, max_depth);
                format!("{} ∨ {}", left_str, right_str)
            }
            Formula::Implies(left, right) => {
                let left_str = Self::wrap_if_compound(left, current_depth, max_depth);
                let right_str = Self::wrap_if_compound(right, current_depth, max_depth);
                format!("{} ⊃ {}", left_str, right_str)
            }
            Formula::Biconditional(left, right) => {
                let left_str = Self::wrap_if_compound(left, current_depth, max_depth);
                let right_str = Self::wrap_if_compound(right, current_depth, max_depth);
                format!("{} ≡ {}", left_str, right_str)
            }
            Formula::Contradiction => "⊥".to_string(),
        }
    }

    /// Get bracket pair based on level from inside out: () innermost, [] middle, {} outermost
    fn brackets_for_level(current_depth: usize, max_depth: usize) -> (&'static str, &'static str) {
        let level_from_inside = max_depth - current_depth - 1;
        match level_from_inside.min(2) {
            0 => ("(", ")"),
            1 => ("[", "]"),
            _ => ("{", "}"),
        }
    }

    /// Wrap in brackets if compound
    /// Uses LOCAL bracket depth of the subformula to determine bracket type
    fn wrap_if_compound(formula: &Formula, _current_depth: usize, _max_depth: usize) -> String {
        match formula {
            Formula::Atom(_) | Formula::Contradiction => formula.display_string(),
            Formula::Not(inner) if matches!(inner.as_ref(), Formula::Atom(_)) => {
                formula.display_string()
            }
            _ => {
                // Use the subformula's LOCAL bracket depth for bracket selection
                let local_depth = formula.bracket_depth();
                let (open, close) = Self::brackets_for_level(0, local_depth + 1);
                let inner = formula.display_string();
                format!("{}{}{}", open, inner, close)
            }
        }
    }

    /// ASCII string with alternating bracket hierarchy: () innermost, [] middle, {} outermost
    /// Every binary subexpression operand is wrapped — no reliance on precedence
    pub fn ascii_string_bracketed(&self) -> String {
        self.ascii_bracketed_inner()
    }

    /// Recursive bracketed formatter using prompt-compatible symbols (. v > <>)
    /// Matches the symbols used in prompt.ts so LLMs see consistent notation.
    fn ascii_bracketed_inner(&self) -> String {
        match self {
            Formula::Atom(name) => name.clone(),
            Formula::Not(inner) => {
                if inner.needs_parens_for_not() {
                    let inner_str = inner.ascii_bracketed_inner();
                    let local_depth = inner.bracket_depth();
                    let (open, close) = Self::brackets_for_level(0, local_depth + 1);
                    format!("~{}{}{}", open, inner_str, close)
                } else {
                    let inner_str = inner.ascii_bracketed_inner();
                    format!("~{}", inner_str)
                }
            }
            Formula::And(left, right) => {
                let left_str = Self::wrap_if_compound_ascii(left);
                let right_str = Self::wrap_if_compound_ascii(right);
                format!("{} . {}", left_str, right_str)
            }
            Formula::Or(left, right) => {
                let left_str = Self::wrap_if_compound_ascii(left);
                let right_str = Self::wrap_if_compound_ascii(right);
                format!("{} v {}", left_str, right_str)
            }
            Formula::Implies(left, right) => {
                let left_str = Self::wrap_if_compound_ascii(left);
                let right_str = Self::wrap_if_compound_ascii(right);
                format!("{} > {}", left_str, right_str)
            }
            Formula::Biconditional(left, right) => {
                let left_str = Self::wrap_if_compound_ascii(left);
                let right_str = Self::wrap_if_compound_ascii(right);
                format!("{} <> {}", left_str, right_str)
            }
            Formula::Contradiction => "#".to_string(),
        }
    }

    /// Wrap in brackets if compound, using LOCAL bracket depth for bracket type selection (ASCII version)
    fn wrap_if_compound_ascii(formula: &Formula) -> String {
        match formula {
            Formula::Atom(_) | Formula::Contradiction => formula.ascii_bracketed_inner(),
            Formula::Not(inner) if matches!(inner.as_ref(), Formula::Atom(_)) => {
                formula.ascii_bracketed_inner()
            }
            _ => {
                let local_depth = formula.bracket_depth();
                let (open, close) = Self::brackets_for_level(0, local_depth + 1);
                let inner = formula.ascii_bracketed_inner();
                format!("{}{}{}", open, inner, close)
            }
        }
    }

    /// ASCII string for parsing/input
    pub fn ascii_string(&self) -> String {
        match self {
            Formula::Atom(name) => name.clone(),
            Formula::Not(inner) => {
                let inner_str = inner.ascii_string();
                if inner.needs_parens_for_not() {
                    format!("~({})", inner_str)
                } else {
                    format!("~{}", inner_str)
                }
            }
            Formula::And(left, right) => {
                let left_str = Self::maybe_paren_ascii(left, self, true);
                let right_str = Self::maybe_paren_ascii(right, self, false);
                format!("{} & {}", left_str, right_str)
            }
            Formula::Or(left, right) => {
                let left_str = Self::maybe_paren_ascii(left, self, true);
                let right_str = Self::maybe_paren_ascii(right, self, false);
                format!("{} | {}", left_str, right_str)
            }
            Formula::Implies(left, right) => {
                let left_str = Self::maybe_paren_ascii(left, self, true);
                let right_str = Self::maybe_paren_ascii(right, self, false);
                format!("{} -> {}", left_str, right_str)
            }
            Formula::Biconditional(left, right) => {
                let left_str = Self::maybe_paren_ascii(left, self, true);
                let right_str = Self::maybe_paren_ascii(right, self, false);
                format!("{} <-> {}", left_str, right_str)
            }
            Formula::Contradiction => "_|_".to_string(),
        }
    }

    fn needs_parens_for_not(&self) -> bool {
        // Show brackets after negation only for binary operators (And, Or, Implies, Biconditional)
        // Atoms, contradictions, and negations don't need brackets: ~~P, ~~~Q, ~_|_
        !matches!(self, Formula::Atom(_) | Formula::Not(_) | Formula::Contradiction)
    }

    fn precedence(&self) -> u8 {
        match self {
            Formula::Atom(_) | Formula::Contradiction => 6,
            Formula::Not(_) => 5,
            Formula::And(_, _) => 4,
            Formula::Or(_, _) => 3,
            Formula::Implies(_, _) => 2,
            Formula::Biconditional(_, _) => 1,
        }
    }

    fn maybe_paren(inner: &Formula, outer: &Formula, is_left: bool) -> String {
        let inner_prec = inner.precedence();
        let outer_prec = outer.precedence();
        let needs_parens = inner_prec < outer_prec
            || (inner_prec == outer_prec && !is_left && matches!(outer, Formula::Implies(_, _)));
        if needs_parens {
            format!("({})", inner.display_string())
        } else {
            inner.display_string()
        }
    }

    fn maybe_paren_ascii(inner: &Formula, outer: &Formula, is_left: bool) -> String {
        let inner_prec = inner.precedence();
        let outer_prec = outer.precedence();
        let needs_parens = inner_prec < outer_prec
            || (inner_prec == outer_prec && !is_left && matches!(outer, Formula::Implies(_, _)));
        if needs_parens {
            format!("({})", inner.ascii_string())
        } else {
            inner.ascii_string()
        }
    }

    /// Get all atomic propositions in the formula
    pub fn atoms(&self) -> HashSet<String> {
        let mut result = HashSet::new();
        self.collect_atoms(&mut result);
        result
    }

    fn collect_atoms(&self, set: &mut HashSet<String>) {
        match self {
            Formula::Atom(name) => {
                set.insert(name.clone());
            }
            Formula::Not(inner) => inner.collect_atoms(set),
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right)
            | Formula::Biconditional(left, right) => {
                left.collect_atoms(set);
                right.collect_atoms(set);
            }
            Formula::Contradiction => {}
        }
    }

    /// Get the depth (nesting level) of the formula
    pub fn depth(&self) -> usize {
        match self {
            Formula::Atom(_) | Formula::Contradiction => 0,
            Formula::Not(inner) => 1 + inner.depth(),
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right)
            | Formula::Biconditional(left, right) => 1 + left.depth().max(right.depth()),
        }
    }

    /// Get the main connective as a string
    pub fn main_connective(&self) -> Option<&'static str> {
        match self {
            Formula::Atom(_) | Formula::Contradiction => None,
            Formula::Not(_) => Some("~"),
            Formula::And(_, _) => Some("·"),
            Formula::Or(_, _) => Some("∨"),
            Formula::Implies(_, _) => Some("⊃"),
            Formula::Biconditional(_, _) => Some("≡"),
        }
    }

    /// Get all subformulas including self
    pub fn subformulas(&self) -> Vec<Formula> {
        let mut result = vec![self.clone()];
        match self {
            Formula::Atom(_) | Formula::Contradiction => {}
            Formula::Not(inner) => {
                result.extend(inner.subformulas());
            }
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right)
            | Formula::Biconditional(left, right) => {
                result.extend(left.subformulas());
                result.extend(right.subformulas());
            }
        }
        result
    }

    /// Get all subformulas with their positional paths from root.
    /// Unlike `subformulas()`, this preserves positional identity —
    /// two structurally identical subtrees get different paths,
    /// allowing targeted replacement of a single occurrence.
    pub fn subformulas_with_paths(&self) -> Vec<(Vec<PathStep>, &Formula)> {
        let mut result = Vec::new();
        self.collect_with_paths(&mut Vec::new(), &mut result);
        result
    }

    fn collect_with_paths<'a>(
        &'a self,
        current_path: &mut Vec<PathStep>,
        result: &mut Vec<(Vec<PathStep>, &'a Formula)>,
    ) {
        result.push((current_path.clone(), self));
        match self {
            Formula::Atom(_) | Formula::Contradiction => {}
            Formula::Not(inner) => {
                current_path.push(PathStep::Inner);
                inner.collect_with_paths(current_path, result);
                current_path.pop();
            }
            Formula::And(left, right)
            | Formula::Or(left, right)
            | Formula::Implies(left, right)
            | Formula::Biconditional(left, right) => {
                current_path.push(PathStep::Left);
                left.collect_with_paths(current_path, result);
                current_path.pop();
                current_path.push(PathStep::Right);
                right.collect_with_paths(current_path, result);
                current_path.pop();
            }
        }
    }

    /// Replace the node at a specific path with a replacement formula.
    /// Only the node at that exact position is replaced — other structurally
    /// identical nodes elsewhere in the tree are left untouched.
    pub fn replace_at_path(&self, path: &[PathStep], replacement: &Formula) -> Formula {
        if path.is_empty() {
            return replacement.clone();
        }

        let step = path[0];
        let rest = &path[1..];

        match (step, self) {
            (PathStep::Inner, Formula::Not(inner)) => {
                Formula::Not(Box::new(inner.replace_at_path(rest, replacement)))
            }
            (PathStep::Left, Formula::And(left, right)) => Formula::And(
                Box::new(left.replace_at_path(rest, replacement)),
                right.clone(),
            ),
            (PathStep::Right, Formula::And(left, right)) => Formula::And(
                left.clone(),
                Box::new(right.replace_at_path(rest, replacement)),
            ),
            (PathStep::Left, Formula::Or(left, right)) => Formula::Or(
                Box::new(left.replace_at_path(rest, replacement)),
                right.clone(),
            ),
            (PathStep::Right, Formula::Or(left, right)) => Formula::Or(
                left.clone(),
                Box::new(right.replace_at_path(rest, replacement)),
            ),
            (PathStep::Left, Formula::Implies(left, right)) => Formula::Implies(
                Box::new(left.replace_at_path(rest, replacement)),
                right.clone(),
            ),
            (PathStep::Right, Formula::Implies(left, right)) => Formula::Implies(
                left.clone(),
                Box::new(right.replace_at_path(rest, replacement)),
            ),
            (PathStep::Left, Formula::Biconditional(left, right)) => Formula::Biconditional(
                Box::new(left.replace_at_path(rest, replacement)),
                right.clone(),
            ),
            (PathStep::Right, Formula::Biconditional(left, right)) => Formula::Biconditional(
                left.clone(),
                Box::new(right.replace_at_path(rest, replacement)),
            ),
            // Path doesn't match formula structure — return unchanged
            _ => self.clone(),
        }
    }

    /// Substitute all occurrences of a variable with a replacement formula
    pub fn substitute(&self, variable: &str, replacement: &Formula) -> Formula {
        match self {
            Formula::Atom(name) => {
                if name == variable {
                    replacement.clone()
                } else {
                    self.clone()
                }
            }
            Formula::Not(inner) => Formula::Not(Box::new(inner.substitute(variable, replacement))),
            Formula::And(left, right) => Formula::And(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Formula::Or(left, right) => Formula::Or(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Formula::Implies(left, right) => Formula::Implies(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Formula::Biconditional(left, right) => Formula::Biconditional(
                Box::new(left.substitute(variable, replacement)),
                Box::new(right.substitute(variable, replacement)),
            ),
            Formula::Contradiction => Formula::Contradiction,
        }
    }

    /// Check if this formula is a negation
    pub fn is_negation(&self) -> bool {
        matches!(self, Formula::Not(_))
    }

    /// Get the inner formula if this is a negation
    pub fn negated_inner(&self) -> Option<&Formula> {
        match self {
            Formula::Not(inner) => Some(inner),
            _ => None,
        }
    }

    /// Create the negation of this formula
    pub fn negate(&self) -> Formula {
        Formula::Not(Box::new(self.clone()))
    }

    /// Check structural equality
    pub fn equals(&self, other: &Formula) -> bool {
        self == other
    }

    /// Compute 32-bit truth table (semantic identity)
    pub fn truth_table(&self) -> u32 {
        crate::services::truth_table::compute_truth_table(self)
    }
}

/// Maximum nesting depth allowed for formulas
const MAX_PARSE_DEPTH: usize = 100;

/// Parser for propositional logic formulas
pub struct FormulaParser<'a> {
    input: &'a str,
    pos: usize,
    depth: usize,
}

#[derive(Debug, Clone)]
pub struct ParseError {
    pub message: String,
    pub position: usize,
}

impl std::fmt::Display for ParseError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Parse error at position {}: {}", self.position, self.message)
    }
}

impl<'a> FormulaParser<'a> {
    pub fn new(input: &'a str) -> Self {
        Self { input, pos: 0, depth: 0 }
    }

    /// Check and increment depth, returning error if too deep
    fn enter_depth(&mut self) -> Result<(), ParseError> {
        self.depth += 1;
        if self.depth > MAX_PARSE_DEPTH {
            return Err(ParseError {
                message: format!("Formula too deeply nested (max {} levels)", MAX_PARSE_DEPTH),
                position: self.pos,
            });
        }
        Ok(())
    }

    /// Decrement depth when leaving a nested construct
    fn exit_depth(&mut self) {
        self.depth = self.depth.saturating_sub(1);
    }

    pub fn parse(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();
        let result = self.parse_biconditional()?;
        self.skip_whitespace();
        if self.pos < self.input.len() {
            return Err(ParseError {
                message: format!("Unexpected character: '{}'", self.current_char().unwrap()),
                position: self.pos,
            });
        }
        Ok(result)
    }

    fn parse_biconditional(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_implication()?;
        self.skip_whitespace();
        while self.matches("<->") || self.matches("≡") || self.matches("<=>") {
            self.enter_depth()?;
            let right = self.parse_implication()?;
            left = Formula::Biconditional(Box::new(left), Box::new(right));
            self.exit_depth();
            self.skip_whitespace();
        }
        Ok(left)
    }

    fn parse_implication(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_disjunction()?;
        self.skip_whitespace();
        // Note: ">" must come after "->" to avoid matching "-" then ">"
        while self.matches("->") || self.matches("⊃") || self.matches("=>") || self.matches(">") {
            self.enter_depth()?;
            let right = self.parse_implication()?; // Right associative
            left = Formula::Implies(Box::new(left), Box::new(right));
            self.exit_depth();
            self.skip_whitespace();
        }
        Ok(left)
    }

    fn parse_disjunction(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_conjunction()?;
        self.skip_whitespace();
        while self.matches("|") || self.matches("∨") || self.matches("v") || self.matches("V") {
            self.enter_depth()?;
            let right = self.parse_conjunction()?;
            left = Formula::Or(Box::new(left), Box::new(right));
            self.exit_depth();
            self.skip_whitespace();
        }
        Ok(left)
    }

    fn parse_conjunction(&mut self) -> Result<Formula, ParseError> {
        let mut left = self.parse_negation()?;
        self.skip_whitespace();
        while self.matches("&") || self.matches("·") || self.matches("^") || self.matches(".") || self.matches("*") {
            self.enter_depth()?;
            let right = self.parse_negation()?;
            left = Formula::And(Box::new(left), Box::new(right));
            self.exit_depth();
            self.skip_whitespace();
        }
        Ok(left)
    }

    fn parse_negation(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();
        if self.matches("~") || self.matches("!") || self.matches("¬") || self.matches("-") {
            self.enter_depth()?;
            let inner = self.parse_negation()?;
            self.exit_depth();
            Ok(Formula::Not(Box::new(inner)))
        } else {
            self.parse_atom()
        }
    }

    fn parse_atom(&mut self) -> Result<Formula, ParseError> {
        self.skip_whitespace();

        // Check for contradiction
        if self.matches("_|_") || self.matches("⊥") || self.matches("#") {
            return Ok(Formula::Contradiction);
        }

        // Check for parenthesized expression (supports (), [], {})
        // Each opens a new depth level to prevent stack overflow from deep nesting
        if self.matches("(") {
            self.enter_depth()?;
            let inner = self.parse_biconditional()?;
            self.skip_whitespace();
            if !self.matches(")") {
                return Err(ParseError {
                    message: "Expected closing parenthesis ')'".to_string(),
                    position: self.pos,
                });
            }
            self.exit_depth();
            return Ok(inner);
        }
        if self.matches("[") {
            self.enter_depth()?;
            let inner = self.parse_biconditional()?;
            self.skip_whitespace();
            if !self.matches("]") {
                return Err(ParseError {
                    message: "Expected closing bracket ']'".to_string(),
                    position: self.pos,
                });
            }
            self.exit_depth();
            return Ok(inner);
        }
        if self.matches("{") {
            self.enter_depth()?;
            let inner = self.parse_biconditional()?;
            self.skip_whitespace();
            if !self.matches("}") {
                return Err(ParseError {
                    message: "Expected closing brace '}'".to_string(),
                    position: self.pos,
                });
            }
            self.exit_depth();
            return Ok(inner);
        }

        // Parse atom name (ASCII alphanumeric only for security)
        let start = self.pos;
        while let Some(c) = self.current_char() {
            if c.is_ascii_alphanumeric() || c == '_' || c == '\'' {
                self.pos += c.len_utf8();
            } else {
                break;
            }
        }

        if self.pos == start {
            return Err(ParseError {
                message: "Expected atom, negation, or parenthesized expression".to_string(),
                position: self.pos,
            });
        }

        Ok(Formula::Atom(self.input[start..self.pos].to_string()))
    }

    fn skip_whitespace(&mut self) {
        while let Some(c) = self.current_char() {
            if c.is_whitespace() {
                self.pos += 1;
            } else {
                break;
            }
        }
    }

    fn current_char(&self) -> Option<char> {
        self.input[self.pos..].chars().next()
    }

    fn matches(&mut self, s: &str) -> bool {
        self.skip_whitespace();
        if self.input[self.pos..].starts_with(s) {
            self.pos += s.len();
            true
        } else {
            false
        }
    }
}

impl Formula {
    /// Parse a formula from a string
    pub fn parse(input: &str) -> Result<Formula, ParseError> {
        // Use char count instead of byte length for proper Unicode handling
        if input.chars().count() > 10000 {
            return Err(ParseError {
                message: "Formula too long (max 10000 chars)".to_string(),
                position: 0,
            });
        }
        let mut parser = FormulaParser::new(input);
        parser.parse()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_parse_atom() {
        let f = Formula::parse("P").unwrap();
        assert_eq!(f, Formula::Atom("P".to_string()));
    }

    #[test]
    fn test_parse_negation() {
        let f = Formula::parse("~P").unwrap();
        assert_eq!(f, Formula::Not(Box::new(Formula::Atom("P".to_string()))));
    }

    #[test]
    fn test_parse_conjunction() {
        let f = Formula::parse("P & Q").unwrap();
        assert_eq!(
            f,
            Formula::And(
                Box::new(Formula::Atom("P".to_string())),
                Box::new(Formula::Atom("Q".to_string()))
            )
        );
    }

    #[test]
    fn test_parse_implication() {
        let f = Formula::parse("P -> Q").unwrap();
        assert_eq!(
            f,
            Formula::Implies(
                Box::new(Formula::Atom("P".to_string())),
                Box::new(Formula::Atom("Q".to_string()))
            )
        );
    }

    #[test]
    fn test_display_string() {
        let f = Formula::Implies(
            Box::new(Formula::And(
                Box::new(Formula::Atom("P".to_string())),
                Box::new(Formula::Atom("Q".to_string())),
            )),
            Box::new(Formula::Atom("R".to_string())),
        );
        // Compound formulas are wrapped with brackets for clarity
        assert_eq!(f.display_string(), "(P . Q) ⊃ R");
    }

    #[test]
    fn test_atoms() {
        let f = Formula::parse("P & Q -> R").unwrap();
        let atoms = f.atoms();
        assert!(atoms.contains("P"));
        assert!(atoms.contains("Q"));
        assert!(atoms.contains("R"));
        assert_eq!(atoms.len(), 3);
    }

    #[test]
    fn test_depth() {
        let f = Formula::parse("P").unwrap();
        assert_eq!(f.depth(), 0);

        let f = Formula::parse("~P").unwrap();
        assert_eq!(f.depth(), 1);

        let f = Formula::parse("P & Q").unwrap();
        assert_eq!(f.depth(), 1);

        let f = Formula::parse("(P & Q) -> R").unwrap();
        assert_eq!(f.depth(), 2);
    }

    #[test]
    fn test_bracket_hierarchy_local_depth() {
        // Bug fix: {[P ∨ Q] . [(~R ⊃ ~P) . R]} was wrong
        // P ∨ Q should use () because its local depth is 0 (atoms don't need brackets)
        // The fix ensures we use LOCAL depth, not global position
        let f = Formula::parse("(P | Q) & ((~R -> ~P) & R)").unwrap();
        let display = f.display_string();

        // P ∨ Q is atomic disjunction → should use ()
        // (~R ⊃ ~P) . R has depth 1 → should use []
        // The outer formula at top level doesn't need extra wrapping
        // Expected: (P ∨ Q) . [(~R ⊃ ~P) . R]
        assert!(display.contains("(P ∨ Q)"), "P ∨ Q should use () not []: {}", display);
        assert!(display.contains("[(~R ⊃ ~P) . R]"), "Nested conjunction should use []: {}", display);
        assert_eq!(display, "(P ∨ Q) . [(~R ⊃ ~P) . R]");
    }

    #[test]
    fn test_simple_subformula_brackets() {
        // Simple case: (P ∨ Q) . R
        // P ∨ Q has local depth 0, so should use ()
        let f = Formula::parse("(P | Q) & R").unwrap();
        let display = f.display_string();
        assert_eq!(display, "(P ∨ Q) . R");
    }

    // ── ascii_string_bracketed tests ──

    #[test]
    fn test_ascii_bracketed_atom() {
        let f = Formula::parse("P").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "P");
    }

    #[test]
    fn test_ascii_bracketed_negation_atom() {
        // ~P should NOT get brackets around the atom
        let f = Formula::parse("~P").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "~P");
    }

    #[test]
    fn test_ascii_bracketed_negation_compound() {
        // ~(P & Q) should bracket the compound
        let f = Formula::parse("~(P & Q)").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "~(P . Q)");
    }

    #[test]
    fn test_ascii_bracketed_simple_binary() {
        // P & Q — outermost not wrapped
        let f = Formula::parse("P & Q").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "P . Q");
    }

    #[test]
    fn test_ascii_bracketed_nested_one_level() {
        // (P | Q) & R — the Or is compound, local depth 0 → ()
        let f = Formula::parse("(P | Q) & R").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "(P v Q) . R");
    }

    #[test]
    fn test_ascii_bracketed_implies_with_and() {
        // (P & Q) -> R — And is compound, local depth 0 → ()
        let f = Formula::parse("(P & Q) -> R").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "(P . Q) > R");
    }

    #[test]
    fn test_ascii_bracketed_two_levels() {
        // ((P | Q) & R) -> S
        // Inner: P v Q wrapped in () (local depth 0)
        // (P v Q) . R is a compound with local depth 1 → [] wrapping
        let f = Formula::parse("((P | Q) & R) -> S").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "[(P v Q) . R] > S");
    }

    #[test]
    fn test_ascii_bracketed_contradiction() {
        let f = Formula::parse("_|_").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "#");
    }

    #[test]
    fn test_ascii_bracketed_biconditional() {
        let f = Formula::parse("P <-> Q").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "P <> Q");
    }

    #[test]
    fn test_ascii_bracketed_local_depth_hierarchy() {
        // (P | Q) & ((~R -> ~P) & R)
        // P v Q: local depth 0 → ()
        // (~R > ~P) . R: local depth 1 → []
        let f = Formula::parse("(P | Q) & ((~R -> ~P) & R)").unwrap();
        let result = f.ascii_string_bracketed();
        assert_eq!(result, "(P v Q) . [(~R > ~P) . R]");
    }

    #[test]
    fn test_ascii_bracketed_double_negation() {
        // ~~P — no brackets needed around negation of negation of atom
        let f = Formula::parse("~~P").unwrap();
        assert_eq!(f.ascii_string_bracketed(), "~~P");
    }
}
