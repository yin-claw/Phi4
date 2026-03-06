# Phi4 Proof-Gap Ledger

Date: 2026-03-06

This file records the current proof boundary on `main`.

## Trust Snapshot

- theorem-level `sorry` in core modules: `12`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `22` (3 now proved)
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

So the project has no hidden axiom-style placeholders, but it is still far from
assumption-free completion. The open mathematics is currently split between:

1. explicit theorem-level frontier statements, and
2. a reduced but still substantial legacy `...Model` assumption surface.

## Explicit Theorem-Level Frontiers

### PROVED (no sorry)

1. `gap_pairing_card` — double factorial count of perfect matchings
2. `gap_wicks_theorem_even` — Wick's theorem for even moments
3. `gap_feynman_graph_expansion` — Feynman graph sum equals Gaussian moment

### OPEN (sorry)

4. `gap_localized_graph_exponential_decay`
5. `gap_covariance_eq_kernel` — requires non-diagonal CLM or ω→0 limit
   (see ProofIdeas/CovarianceMismatch.md)
6. `gap_hasExpInteractionLp` — **WP1 blocker** (Chapter 8)
7. `gap_schwingerTwo_le_free`
8. `gap_hasSchwingerNMonotone`
9. `gap_hasChessboardEstimate`
10. `gap_hasSchwingerUniformBound`
11. `gap_free_covariance_reflection_positive`
    (1D Green's function factorization infrastructure in GreenFunction/OneDimGreen.lean)
12. `gap_dirichlet_covariance_reflection_positive`
13. `gap_interacting_measure_reflection_positive`
14. `gap_infiniteVolumeLimit_exists`
15. `gap_wick_powers_infinite_volume`
16. `gap_wickCubicSmeared_tendsto_ae`
17. `gap_euclidean_equation_of_motion`
18. `gap_generating_functional_bound`
19. `gap_generating_functional_bound_uniform`
20. `gap_nonlocal_phi4_bound`
21. `gap_measure_os3_reflection_positive`
22. `gap_phi4_linear_growth`

## Explicit But Not Yet Named OS Obligations

The OS-side chain is not fully captured by `gap_*` names yet. The following
explicit obligations still appear as direct hypotheses in the local assembly
theorems:

- OS0 continuity of `phi4SchwingerFunctions`
- OS2 translation covariance
- OS2 rotation covariance
- distributional E2 reflection positivity
- E3 permutation symmetry

## Remaining Legacy Interface Debt

The dominant unsurfaced proof debt still sits in model classes, including:

- interaction interfaces,
- covariance/kernel interfaces,
- correlation inequality interfaces,
- infinite-volume measure/moment interfaces,
- regularity interfaces.

This means theorem-level frontiers are now more visible than before, but they do
not yet cover the full mathematical debt of the repository.

## Main Risk

WP1 remains the primary blocker:
- proving the finite-volume Boltzmann-weight integrability and normalization
  needed for the interacting measure.

Everything downstream depends on that analytic core.
