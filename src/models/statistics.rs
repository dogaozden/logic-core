use serde::{Deserialize, Serialize};
use chrono::{DateTime, Utc};
use std::collections::HashMap;
use super::theorem::{Difficulty, Theme};
use super::rules::inference::InferenceRule;
use super::rules::equivalence::EquivalenceRule;
use super::rules::technique::ProofTechnique;

/// Statistics for a specific difficulty level
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct DifficultyStats {
    pub attempted: u32,
    pub completed: u32,
    pub average_time_secs: Option<f64>,
    pub average_steps: Option<f64>,
}

impl DifficultyStats {
    pub fn success_rate(&self) -> f64 {
        if self.attempted == 0 {
            0.0
        } else {
            self.completed as f64 / self.attempted as f64
        }
    }
}

/// Statistics for a specific theme
#[derive(Debug, Clone, Default, Serialize, Deserialize)]
pub struct ThemeStats {
    pub attempted: u32,
    pub completed: u32,
}

impl ThemeStats {
    pub fn success_rate(&self) -> f64 {
        if self.attempted == 0 {
            0.0
        } else {
            self.completed as f64 / self.attempted as f64
        }
    }
}

/// Record of a single proof attempt
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct ProofAttempt {
    pub theorem_id: String,
    pub started_at: DateTime<Utc>,
    pub completed_at: Option<DateTime<Utc>>,
    pub completed: bool,
    pub steps: u32,
    pub hints_used: u32,
    pub rules_used: Vec<String>,
}

impl ProofAttempt {
    pub fn new(theorem_id: String) -> Self {
        Self {
            theorem_id,
            started_at: Utc::now(),
            completed_at: None,
            completed: false,
            steps: 0,
            hints_used: 0,
            rules_used: Vec::new(),
        }
    }

    pub fn complete(&mut self) {
        self.completed = true;
        self.completed_at = Some(Utc::now());
    }

    pub fn duration_secs(&self) -> Option<f64> {
        self.completed_at.map(|end| {
            (end - self.started_at).num_milliseconds() as f64 / 1000.0
        })
    }
}

/// Overall user statistics
#[derive(Debug, Clone, Serialize, Deserialize)]
pub struct UserStatistics {
    pub total_proofs_attempted: u32,
    pub total_proofs_completed: u32,
    pub current_streak: u32,
    pub longest_streak: u32,
    pub last_proof_date: Option<DateTime<Utc>>,
    pub difficulty_stats: HashMap<String, DifficultyStats>,
    pub theme_stats: HashMap<String, ThemeStats>,
    pub rule_usage: HashMap<String, u32>,
    pub recent_attempts: Vec<ProofAttempt>,
}

impl Default for UserStatistics {
    fn default() -> Self {
        Self {
            total_proofs_attempted: 0,
            total_proofs_completed: 0,
            current_streak: 0,
            longest_streak: 0,
            last_proof_date: None,
            difficulty_stats: HashMap::new(),
            theme_stats: HashMap::new(),
            rule_usage: HashMap::new(),
            recent_attempts: Vec::new(),
        }
    }
}

impl UserStatistics {
    pub fn new() -> Self {
        Self::default()
    }

    pub fn overall_success_rate(&self) -> f64 {
        if self.total_proofs_attempted == 0 {
            0.0
        } else {
            self.total_proofs_completed as f64 / self.total_proofs_attempted as f64
        }
    }

    pub fn record_attempt(&mut self, attempt: ProofAttempt, difficulty: Difficulty, theme: Option<Theme>) {
        self.total_proofs_attempted += 1;

        if attempt.completed {
            self.total_proofs_completed += 1;
            self.update_streak();
        }

        // Update difficulty stats
        let diff_key = format!("{:?}", difficulty).to_lowercase();
        let diff_stats = self.difficulty_stats.entry(diff_key).or_default();
        diff_stats.attempted += 1;
        if attempt.completed {
            diff_stats.completed += 1;
            if let Some(duration) = attempt.duration_secs() {
                let n = diff_stats.completed as f64;
                let current_avg = diff_stats.average_time_secs.unwrap_or(0.0);
                diff_stats.average_time_secs = Some((current_avg * (n - 1.0) + duration) / n);
            }
            let n = diff_stats.completed as f64;
            let current_avg = diff_stats.average_steps.unwrap_or(0.0);
            diff_stats.average_steps = Some((current_avg * (n - 1.0) + attempt.steps as f64) / n);
        }

        // Update theme stats
        if let Some(theme) = theme {
            let theme_key = format!("{:?}", theme);
            let theme_stats = self.theme_stats.entry(theme_key).or_default();
            theme_stats.attempted += 1;
            if attempt.completed {
                theme_stats.completed += 1;
            }
        }

        // Update rule usage
        for rule in &attempt.rules_used {
            *self.rule_usage.entry(rule.clone()).or_insert(0) += 1;
        }

        // Keep recent attempts (last 50)
        self.recent_attempts.push(attempt);
        if self.recent_attempts.len() > 50 {
            self.recent_attempts.remove(0);
        }
    }

    fn update_streak(&mut self) {
        let today = Utc::now().date_naive();

        if let Some(last_date) = self.last_proof_date {
            let last_day = last_date.date_naive();
            let diff = (today - last_day).num_days();

            if diff == 0 {
                // Same day, streak continues
            } else if diff == 1 {
                // Consecutive day, increment streak
                self.current_streak += 1;
            } else {
                // Streak broken, reset to 1
                self.current_streak = 1;
            }
        } else {
            // First proof
            self.current_streak = 1;
        }

        self.longest_streak = self.longest_streak.max(self.current_streak);
        self.last_proof_date = Some(Utc::now());
    }

    pub fn get_difficulty_stats(&self, difficulty: Difficulty) -> DifficultyStats {
        let key = format!("{:?}", difficulty).to_lowercase();
        self.difficulty_stats.get(&key).cloned().unwrap_or_default()
    }

    pub fn get_theme_stats(&self, theme: Theme) -> ThemeStats {
        let key = format!("{:?}", theme);
        self.theme_stats.get(&key).cloned().unwrap_or_default()
    }

    pub fn most_used_rules(&self, count: usize) -> Vec<(String, u32)> {
        let mut rules: Vec<_> = self.rule_usage.iter().map(|(k, v)| (k.clone(), *v)).collect();
        rules.sort_by(|a, b| b.1.cmp(&a.1));
        rules.truncate(count);
        rules
    }

    pub fn record_rule_usage(&mut self, rule: &str) {
        *self.rule_usage.entry(rule.to_string()).or_insert(0) += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_record_attempt() {
        let mut stats = UserStatistics::new();
        let mut attempt = ProofAttempt::new("test-1".to_string());
        attempt.complete();
        attempt.steps = 5;

        stats.record_attempt(attempt, Difficulty::Easy, Some(Theme::ModusPonens));

        assert_eq!(stats.total_proofs_attempted, 1);
        assert_eq!(stats.total_proofs_completed, 1);
        assert_eq!(stats.current_streak, 1);

        let diff_stats = stats.get_difficulty_stats(Difficulty::Easy);
        assert_eq!(diff_stats.attempted, 1);
        assert_eq!(diff_stats.completed, 1);
    }

    #[test]
    fn test_success_rate() {
        let mut stats = UserStatistics::new();

        // Add 2 completed and 1 incomplete
        for i in 0..3 {
            let mut attempt = ProofAttempt::new(format!("test-{}", i));
            if i < 2 {
                attempt.complete();
            }
            stats.record_attempt(attempt, Difficulty::Easy, None);
        }

        let rate = stats.overall_success_rate();
        assert!((rate - 0.666).abs() < 0.01);
    }
}
