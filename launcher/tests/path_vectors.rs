//! `path_clean` against Lean (CODEC-27). Every row of `PATH_VECTORS` is a path with the verdict that
//! Lean's path decoder gives it (`Codec.Path.split`, then `Codec.Path.clean` on each component). The
//! verdicts are evaluated by `emit-hosting` when it prints `generated.rs`. The Rust rule is a template in
//! the emitter, so this test is what ties it to Lean's rule.
//!
//! Refuses: a `path_clean` that accepts a path Lean refuses, or refuses a path Lean accepts, on any row. It
//! also refuses a vector table with only one verdict.

use nanodregg_launcher::generated::wire::{PATH_VECTORS, path_clean};

#[test]
fn path_clean_is_leans_rule() {
    assert!(PATH_VECTORS.iter().any(|(_, ok)| *ok) && PATH_VECTORS.iter().any(|(_, ok)| !*ok));
    for (v, ok) in PATH_VECTORS {
        assert_eq!(path_clean(v), *ok, "path {:?}", String::from_utf8_lossy(v));
    }
}
