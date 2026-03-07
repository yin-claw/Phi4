# Phi4 Audit Notes

Date: 2026-03-06

## Main vs Simplified Branch Review

The `simplified` branch was reviewed before any salvage back to `main`.

### Safe material imported into `main`

1. clearer documentation for `limsup`-based staging definitions,
2. explicit bridge lemmas from `limsup` definitions to ordinary limits under convergence,
3. explicit theorem-level frontier statements for several model-only obligations,
4. corrected status documentation and roadmap framing.

### Material intentionally not imported

The branch also deleted substantive proved mathematics, so it was not suitable
for direct merge. In particular:

1. `Phi4/FeynmanGraphs/LocalizedBounds.lean` was removed even though it contains
   real combinatorial/localized-bound infrastructure,
2. parts of `Phi4/InfiniteVolumeLimit/Part2.lean` and `Part3.lean` with genuine
   cumulant/positivity lemmas were removed,
3. parts of `Phi4/Interaction/Part1Tail.lean` were dropped even though they
   contain real tail/moment infrastructure.

## Current Honest Status

- theorem-level `sorry` in core modules: `18`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `33`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

## Audit Conclusion

`main` is now more honest than it was before the branch comparison, because the
open mathematics is no longer presented as “zero sorry therefore nearly done”.

Recent local cleanup also deleted dead OS/reconstruction bundle classes and the
unused `Phi4ModelBundle` file. The latest pass also removed the internal
infinite-volume recombination classes and dead correlation bridge classes, so
the remaining model-class surface is smaller and closer to the actual live
dependency graph. The current slice also removed `MultipleReflectionModel` from
the infinite-volume limit arguments and surfaced the chessboard estimate itself
as the explicit frontier `gap_hasChessboardEstimate`. More recently, several
WP1 analytic-input obligations were surfaced explicitly in
`Interaction/AnalyticInputs.lean`, which increased the visible frontier count
without changing the no-axiom / no-`def := by sorry` trust boundary.

The latest proof-focused pass also closed `gap_interaction_sq_integrable` and
added quantitative shell infrastructure in `WickProduct.lean`, including:

1. `wickPower_four_step_decomposition`,
2. `rawFieldEval_sub_sq_expectation`,
3. `rawFieldEval_sub_fourth_expectation`.

This means the main WP1 shell-rate blocker is no longer stuck on quartic-Wick
algebra or basic Gaussian moment identities. The remaining obstruction is the
actual covariance-shell analysis needed for
`gap_interactionCutoff_standardSeq_L2_increment_rate`.

But the repository is still not close to completion:

1. several major frontiers are now explicit theorem-level gaps,
2. several OS-side obligations are explicit hypotheses but not yet named local frontiers,
3. WP1 remains the controlling analytic blocker.
