use serde::{Deserialize, Serialize};
use super::formula::Formula;
use super::rules::technique::ProofTechnique;

/// Represents a proof scope (subproof)
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofScope {
    pub id: String,
    pub start_line: usize,
    pub end_line: Option<usize>,
    pub assumption: Formula,
    pub technique: ProofTechnique,
    pub depth: usize,
    pub parent_scope_id: Option<String>,
}

impl ProofScope {
    pub fn new(
        id: String,
        start_line: usize,
        assumption: Formula,
        technique: ProofTechnique,
        depth: usize,
        parent_scope_id: Option<String>,
    ) -> Self {
        Self {
            id,
            start_line,
            end_line: None,
            assumption,
            technique,
            depth,
            parent_scope_id,
        }
    }

    pub fn is_open(&self) -> bool {
        self.end_line.is_none()
    }

    pub fn close(&mut self, end_line: usize) {
        self.end_line = Some(end_line);
    }

    pub fn contains_line(&self, line_number: usize) -> bool {
        if let Some(end) = self.end_line {
            line_number >= self.start_line && line_number <= end
        } else {
            line_number >= self.start_line
        }
    }
}

/// Manages proof scopes and accessibility
#[derive(Debug, Clone, Serialize, Deserialize, Default)]
pub struct ScopeManager {
    scopes: Vec<ProofScope>,
    next_scope_id: usize,
}

impl ScopeManager {
    pub fn new() -> Self {
        Self {
            scopes: Vec::new(),
            next_scope_id: 1,
        }
    }

    /// Open a new subproof scope
    pub fn open_scope(
        &mut self,
        start_line: usize,
        assumption: Formula,
        technique: ProofTechnique,
    ) -> String {
        let depth = self.current_depth() + 1;
        let parent_id = self.current_scope_id();
        let scope_id = format!("scope-{}", self.next_scope_id);
        self.next_scope_id += 1;

        let scope = ProofScope::new(
            scope_id.clone(),
            start_line,
            assumption,
            technique,
            depth,
            parent_id,
        );

        self.scopes.push(scope);
        scope_id
    }

    /// Close the current (innermost open) scope
    pub fn close_scope(&mut self, end_line: usize) -> Option<&ProofScope> {
        // Find the innermost open scope
        for scope in self.scopes.iter_mut().rev() {
            if scope.is_open() {
                scope.close(end_line);
                return Some(scope);
            }
        }
        None
    }

    /// Remove the latest scope (used when undoing an assumption)
    pub fn pop_scope(&mut self, start_line: usize) -> Option<ProofScope> {
        // Only pop if the last scope matches the start line and is open
        if let Some(pos) = self.scopes.iter().rposition(|s| s.start_line == start_line && s.is_open()) {
            return Some(self.scopes.remove(pos));
        }
        None
    }

    /// Get the current depth (number of open scopes)
    pub fn current_depth(&self) -> usize {
        self.scopes.iter().filter(|s| s.is_open()).count()
    }

    /// Get the current scope ID (innermost open scope)
    pub fn current_scope_id(&self) -> Option<String> {
        self.scopes
            .iter()
            .rev()
            .find(|s| s.is_open())
            .map(|s| s.id.clone())
    }

    /// Get the current scope
    pub fn current_scope(&self) -> Option<&ProofScope> {
        self.scopes.iter().rev().find(|s| s.is_open())
    }

    /// Get scope by ID
    pub fn get_scope(&self, scope_id: &str) -> Option<&ProofScope> {
        self.scopes.iter().find(|s| s.id == scope_id)
    }

    /// Get the depth of a specific line
    pub fn depth_at_line(&self, line_number: usize) -> usize {
        self.scopes
            .iter()
            .filter(|s| s.contains_line(line_number))
            .count()
    }

    /// Check if a line is accessible from another line
    pub fn is_accessible(&self, from_line: usize, to_line: usize) -> bool {
        if to_line >= from_line {
            return false; // Can only reference earlier lines
        }

        // Get the scope of the target line
        let target_scopes: Vec<&ProofScope> = self
            .scopes
            .iter()
            .filter(|s| s.contains_line(to_line))
            .collect();


        // A line is accessible if all its scopes are either:
        // 1. Still open (from current line's perspective)
        // 2. Contain the current line as well
        for target_scope in &target_scopes {
            // If the target scope is closed before the current line, it's not accessible
            if let Some(end) = target_scope.end_line {
                if end < from_line {
                    return false;
                }
            }
            // If target scope doesn't contain current line and is closed, not accessible
            if !target_scope.contains_line(from_line) {
                return false;
            }
        }

        true
    }

    /// Check if a subproof (from start_line to end_line) is accessible from a given line
    pub fn is_subproof_accessible(&self, from_line: usize, start_line: usize, end_line: usize) -> bool {
        // The subproof must be entirely before the current line
        if end_line >= from_line {
            return false;
        }

        // Find the scope that corresponds to this subproof
        let subproof_scope = self.scopes.iter().find(|s| {
            s.start_line == start_line && s.end_line == Some(end_line)
        });

        if let Some(scope) = subproof_scope {
            // The subproof is accessible if its parent scope (if any) contains the current line
            if let Some(parent_id) = &scope.parent_scope_id {
                if let Some(parent) = self.get_scope(parent_id) {
                    return parent.contains_line(from_line);
                }
            }
            // If no parent scope, check if we're at the main proof level
            return self.depth_at_line(from_line) == 0 ||
                   self.scopes.iter().any(|s| s.contains_line(from_line) && s.depth < scope.depth);
        }

        false
    }

    /// Get all scopes
    pub fn all_scopes(&self) -> &[ProofScope] {
        &self.scopes
    }

    /// Check if there are any open scopes
    pub fn has_open_scopes(&self) -> bool {
        self.scopes.iter().any(|s| s.is_open())
    }

    /// Reset the scope manager
    pub fn reset(&mut self) {
        self.scopes.clear();
        self.next_scope_id = 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::models::formula::Formula;

    #[test]
    fn test_open_scope() {
        let mut manager = ScopeManager::new();
        let id = manager.open_scope(
            1,
            Formula::parse("P").unwrap(),
            ProofTechnique::ConditionalProof,
        );
        assert_eq!(manager.current_depth(), 1);
        assert_eq!(manager.current_scope_id(), Some(id));
    }

    #[test]
    fn test_close_scope() {
        let mut manager = ScopeManager::new();
        manager.open_scope(1, Formula::parse("P").unwrap(), ProofTechnique::ConditionalProof);
        manager.close_scope(3);
        assert_eq!(manager.current_depth(), 0);
        assert!(!manager.has_open_scopes());
    }

    #[test]
    fn test_nested_scopes() {
        let mut manager = ScopeManager::new();
        let outer = manager.open_scope(1, Formula::parse("P").unwrap(), ProofTechnique::ConditionalProof);
        let inner = manager.open_scope(2, Formula::parse("Q").unwrap(), ProofTechnique::ConditionalProof);

        assert_eq!(manager.current_depth(), 2);
        assert_eq!(manager.current_scope_id(), Some(inner.clone()));

        manager.close_scope(4);
        assert_eq!(manager.current_depth(), 1);
        assert_eq!(manager.current_scope_id(), Some(outer));
    }

    #[test]
    fn test_accessibility() {
        let mut manager = ScopeManager::new();
        manager.open_scope(2, Formula::parse("P").unwrap(), ProofTechnique::ConditionalProof);
        manager.close_scope(4);

        // Line 1 (before scope) is accessible from line 5
        assert!(manager.is_accessible(5, 1));

        // Line 3 (inside closed scope) is NOT accessible from line 5
        assert!(!manager.is_accessible(5, 3));
    }
}
