# Phi4: Formal Construction of the φ⁴₂ Quantum Field Theory

A Lean 4 formalization of constructive 2D φ⁴ Euclidean QFT aimed at the Glimm-Jaffe pipeline:

1. construct the infinite-volume Schwinger functions,
2. prove the Osterwalder-Schrader axioms,
3. reconstruct the corresponding Wightman theory.

## Current Status (March 5, 2026)

- Core theorem-level `sorry` in `Phi4/**/*.lean` excluding `Phi4/Scratch`: `10`
- Legacy `class/structure .*Model` declarations: `48`
- Canonical `gap_*` theorem frontiers: `18`
- `axiom` declarations: `0`
- `def`/`abbrev := by sorry`: `0`

This is not a completed construction.

The correct status framing is:
- there are no hidden axiom-style placeholders,
- the open mathematics is now partly surfaced as explicit theorem-level frontiers,
- a large legacy assumption surface still remains in `...Model` classes.

## Roadmap To OS Axioms

1. `WP1`: prove `gap_hasExpInteractionLp`.
   This is the Chapter 8 finite-volume integrability/normalization core.
2. `WP2`: close finite-volume monotonicity, comparison, chessboard, and reflection-positivity frontiers.
   Main explicit targets:
   - `gap_hasSchwingerNMonotone`
   - `gap_hasSchwingerUniformBound`
   - `gap_schwingerTwo_le_free`
   - `gap_free_covariance_reflection_positive`
   - `gap_dirichlet_covariance_reflection_positive`
   - `gap_interacting_measure_reflection_positive`
3. `WP3`: construct the infinite-volume Schwinger package and its representing measure.
   Current explicit endpoint:
   - `gap_infiniteVolumeSchwingerModel_nonempty`
4. `WP4`: close regularity and equation-of-motion frontiers.
   Main explicit targets:
   - `gap_wick_powers_infinite_volume`
   - `gap_wickCubicSmeared_tendsto_ae`
   - `gap_euclidean_equation_of_motion`
   - `gap_generating_functional_bound`
5. `WP5`: close OS packaging and reconstruction.
   Main explicit targets:
   - `gap_osaCoreModel_nonempty`
   - `gap_osDistributionE2_nonempty`
   - `gap_osE4Cluster_nonempty`
   - `gap_phi4_linear_growth`

## Main Architectural Constraint

`main` still contains a large legacy interface layer. The active direction is:

1. add explicit theorem-level frontier statements,
2. migrate callers away from legacy model classes,
3. delete superseded wrappers and interface-only proof debt.

The `simplified` branch was not merged wholesale because it mixed useful theorem-surface cleanup with deletion of substantive proved mathematics.
