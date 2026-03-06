# TODO: φ⁴₂ Development Plan

Date: 2026-03-06

## Baseline

- theorem-level `sorry` in core modules: `12`
- legacy `...Model` classes: `13`
- canonical `gap_*` theorem frontiers: `22` (3 proved, 19 open)
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

## Recent Progress (2026-03-06)

- **PROVED** `gap_pairing_card`, `gap_wicks_theorem_even`, `gap_feynman_graph_expansion`
- **NEW** `covariance_spectral_sum`: correct spectral formula for harmonic oscillator covariance
- **NEW** `GreenFunction/OneDimGreen.lean`: 1D Green's function factorization and RP
- **DOCUMENTED** `freeCovarianceCLM`/`freeCovKernel` mismatch (see ProofIdeas/CovarianceMismatch.md)

## Priority Order

1. Close WP1 interaction-integrability frontiers.
2. Convert remaining model-only bottlenecks into explicit theorem frontiers.
3. Close finite-volume monotonicity/comparison/RP frontiers.
4. Close infinite-volume moment/measure representation.
5. Close regularity and linear-growth frontiers.
6. Only then reduce residual legacy model-class surface.

## Immediate Queue

1. `Phi4/Interaction/Part1Core.lean`
   - prove `gap_hasExpInteractionLp`
   - keep theorems assumption-explicit
2. `Phi4/CorrelationInequalities.lean`
   - prove `gap_hasSchwingerNMonotone`
3. `Phi4/MultipleReflections.lean`
   - prove `gap_hasSchwingerUniformBound`
4. `Phi4/FiniteVolumeMeasure.lean`
   - prove `gap_schwingerTwo_le_free`
5. `Phi4/ReflectionPositivity.lean`
   - prove the three RP frontier theorems
6. `Phi4/Regularity.lean`
   - prove Wick-power / Wick-cubic / EOM frontiers

## Conversion Work

The repository still has many obligations encoded only as `...Model` fields.
Those should be converted module-by-module into theorem-level frontiers with
sound statements and theorem-level `by sorry` only where genuinely open.

The next conversion targets after the finite-volume frontiers are:

1. covariance/kernel bridges,
2. infinite-volume moment representation,
3. OS packaging subinterfaces,
4. reconstruction weak-coupling/linear-growth inputs.

## Rules For This Phase

1. No new `...Model` classes.
2. No wrapper-for-wrapper route additions.
3. No theorem weakening for convenience.
4. Prefer theorem-level gaps to hidden interface debt.
5. Do not delete substantive proof content in the name of debloating.
