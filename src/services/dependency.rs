use std::collections::{HashMap, HashSet};

/// Tracks dependencies between proof lines for cascading invalidation
#[derive(Debug, Clone, Default)]
pub struct DependencyTracker {
    /// Maps each line to the lines it depends on
    dependencies: HashMap<usize, HashSet<usize>>,
    /// Maps each line to the lines that depend on it
    dependents: HashMap<usize, HashSet<usize>>,
}

impl DependencyTracker {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a dependency: `line` depends on `depends_on`
    pub fn add_dependency(&mut self, line: usize, depends_on: usize) {
        self.dependencies
            .entry(line)
            .or_default()
            .insert(depends_on);

        self.dependents
            .entry(depends_on)
            .or_default()
            .insert(line);
    }

    /// Add multiple dependencies for a line
    pub fn add_dependencies(&mut self, line: usize, depends_on: &[usize]) {
        for &dep in depends_on {
            self.add_dependency(line, dep);
        }
    }

    /// Remove a line and all its dependencies
    pub fn remove_line(&mut self, line: usize) {
        // Remove this line from its dependencies' dependents
        if let Some(deps) = self.dependencies.remove(&line) {
            for dep in deps {
                if let Some(dep_dependents) = self.dependents.get_mut(&dep) {
                    dep_dependents.remove(&line);
                }
            }
        }

        // Remove this line from dependents
        self.dependents.remove(&line);
    }

    /// Get all lines that depend on the given line (direct dependents only)
    pub fn direct_dependents(&self, line: usize) -> HashSet<usize> {
        self.dependents.get(&line).cloned().unwrap_or_default()
    }

    /// Get all lines that the given line depends on
    pub fn direct_dependencies(&self, line: usize) -> HashSet<usize> {
        self.dependencies.get(&line).cloned().unwrap_or_default()
    }

    /// Get all lines that depend on the given line (transitively)
    pub fn all_dependents(&self, line: usize) -> HashSet<usize> {
        let mut result = HashSet::new();
        let mut to_visit = vec![line];

        while let Some(current) = to_visit.pop() {
            if let Some(deps) = self.dependents.get(&current) {
                for &dep in deps {
                    if result.insert(dep) {
                        to_visit.push(dep);
                    }
                }
            }
        }

        result
    }

    /// Get all lines affected by invalidating the given line (cascade)
    pub fn cascade_invalidation(&self, line: usize) -> Vec<usize> {
        let mut affected: Vec<usize> = self.all_dependents(line).into_iter().collect();
        affected.sort();
        affected
    }

    /// Check for cycles in dependencies (should not happen in a valid proof)
    pub fn has_cycle(&self) -> bool {
        let mut visited = HashSet::new();
        let mut rec_stack = HashSet::new();

        for &node in self.dependencies.keys() {
            if self.has_cycle_from(node, &mut visited, &mut rec_stack) {
                return true;
            }
        }

        false
    }

    fn has_cycle_from(
        &self,
        node: usize,
        visited: &mut HashSet<usize>,
        rec_stack: &mut HashSet<usize>,
    ) -> bool {
        if rec_stack.contains(&node) {
            return true;
        }
        if visited.contains(&node) {
            return false;
        }

        visited.insert(node);
        rec_stack.insert(node);

        if let Some(deps) = self.dependents.get(&node) {
            for &dep in deps {
                if self.has_cycle_from(dep, visited, rec_stack) {
                    return true;
                }
            }
        }

        rec_stack.remove(&node);
        false
    }

    /// Get topological order of lines (dependencies before dependents)
    pub fn topological_order(&self) -> Vec<usize> {
        let mut in_degree: HashMap<usize, usize> = HashMap::new();
        let mut all_nodes: HashSet<usize> = HashSet::new();

        // Collect all nodes
        for (&node, deps) in &self.dependencies {
            all_nodes.insert(node);
            for &dep in deps {
                all_nodes.insert(dep);
            }
        }

        // Calculate in-degrees
        for &node in &all_nodes {
            in_degree.insert(node, 0);
        }
        for deps in self.dependents.values() {
            for &dep in deps {
                *in_degree.entry(dep).or_insert(0) += 1;
            }
        }

        // Start with nodes that have no dependencies
        let mut queue: Vec<usize> = in_degree
            .iter()
            .filter(|(_, &deg)| deg == 0)
            .map(|(&node, _)| node)
            .collect();
        queue.sort();

        let mut result = Vec::new();

        while let Some(node) = queue.pop() {
            result.push(node);

            if let Some(deps) = self.dependents.get(&node) {
                for &dep in deps {
                    if let Some(deg) = in_degree.get_mut(&dep) {
                        *deg -= 1;
                        if *deg == 0 {
                            queue.push(dep);
                            queue.sort_by(|a, b| b.cmp(a)); // Keep sorted in reverse
                        }
                    }
                }
            }
        }

        result
    }

    /// Clear all dependencies
    pub fn clear(&mut self) {
        self.dependencies.clear();
        self.dependents.clear();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_add_dependency() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency(3, 1);
        tracker.add_dependency(3, 2);

        let deps = tracker.direct_dependencies(3);
        assert!(deps.contains(&1));
        assert!(deps.contains(&2));

        let dependents = tracker.direct_dependents(1);
        assert!(dependents.contains(&3));
    }

    #[test]
    fn test_cascade_invalidation() {
        let mut tracker = DependencyTracker::new();
        // Line 3 depends on 1 and 2
        tracker.add_dependencies(3, &[1, 2]);
        // Line 4 depends on 3
        tracker.add_dependency(4, 3);
        // Line 5 depends on 4
        tracker.add_dependency(5, 4);

        // Invalidating line 1 should cascade to 3, 4, 5
        let affected = tracker.cascade_invalidation(1);
        assert!(affected.contains(&3));
        assert!(affected.contains(&4));
        assert!(affected.contains(&5));
    }

    #[test]
    fn test_no_cycle() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency(2, 1);
        tracker.add_dependency(3, 2);
        tracker.add_dependency(4, 3);

        assert!(!tracker.has_cycle());
    }

    #[test]
    fn test_topological_order() {
        let mut tracker = DependencyTracker::new();
        tracker.add_dependency(2, 1);
        tracker.add_dependency(3, 2);
        tracker.add_dependency(4, 2);

        let order = tracker.topological_order();
        // 1 should come before 2, 2 before 3 and 4
        let pos_1 = order.iter().position(|&x| x == 1).unwrap();
        let pos_2 = order.iter().position(|&x| x == 2).unwrap();
        let pos_3 = order.iter().position(|&x| x == 3).unwrap();
        let pos_4 = order.iter().position(|&x| x == 4).unwrap();

        assert!(pos_1 < pos_2);
        assert!(pos_2 < pos_3);
        assert!(pos_2 < pos_4);
    }
}
