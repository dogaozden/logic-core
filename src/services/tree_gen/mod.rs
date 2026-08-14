mod context;
mod backward;
mod templates;
mod builder;

pub use context::{
    ConstructionContext,
    RequiredTechniques,
    GenerationError,
    TreeGenConfig,
    TAUTOLOGY,
};
pub use builder::ProofTreeGenerator;

// Re-export for backward compatibility
pub use backward::backward_construct;
