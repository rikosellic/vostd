/// Exclusive ownership resource.
pub mod excl;
/// Fractional ownership.
pub mod frac;
/// Product of a PCM and a storage-protocol resource algebra.
pub mod hybrid_product;
/// Token that maintains access to the sum type of two resources.
pub mod sum;
/// A wrapper around `vstd::tokens::FracGhost` that stores and dispatches fractional access.
pub mod tokens;
