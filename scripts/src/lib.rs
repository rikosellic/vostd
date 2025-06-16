pub mod error;
pub mod manifest;
pub mod gits;
pub mod git;

pub mod prelude {
    pub use super::error::*;
    pub use super::manifest::*;
    pub use super::gits;
    pub use super::git;
}