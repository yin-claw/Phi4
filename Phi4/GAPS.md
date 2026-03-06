# Phi4 Proof-Gap Ledger

Date: 2026-03-05

This file records the current proof boundary on `main`.

## Trust Snapshot

- theorem-level `sorry` in core modules: `10`
- legacy `class/structure .*Model`: `48`
- canonical `gap_*` theorem frontiers: `18`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

So the project has no hidden axiom-style placeholders, but it is still far from
assumption-free completion. The open mathematics is currently split between:

1. explicit theorem-level frontier statements, and
2. a substantial remaining legacy `...Model` assumption surface.

## Explicit Theorem-Level Frontiers

1. `gap_hasExpInteractionLp`
2. `gap_hasSchwingerNMonotone`
3. `gap_hasSchwingerUniformBound`
4. `gap_schwingerTwo_le_free`
5. `gap_free_covariance_reflection_positive`
6. `gap_dirichlet_covariance_reflection_positive`
7. `gap_interacting_measure_reflection_positive`
8. `gap_infiniteVolumeSchwingerModel_nonempty`
9. `gap_wick_powers_infinite_volume`
10. `gap_wickCubicSmeared_tendsto_ae`
11. `gap_euclidean_equation_of_motion`
12. `gap_generating_functional_bound`
13. `gap_generating_functional_bound_uniform`
14. `gap_nonlocal_phi4_bound`
15. `gap_osaCoreModel_nonempty`
16. `gap_osDistributionE2_nonempty`
17. `gap_osE4Cluster_nonempty`
18. `gap_phi4_linear_growth`

## Remaining Legacy Interface Debt

The dominant unsurfaced proof debt still sits in model classes, including:

- interaction interfaces,
- covariance/kernel interfaces,
- correlation inequality interfaces,
- infinite-volume measure/moment interfaces,
- regularity/OS interfaces,
- reconstruction interfaces.

This means theorem-level frontiers are now more visible than before, but they do
not yet cover the full mathematical debt of the repository.

## Main Risk

WP1 remains the primary blocker:
- proving the finite-volume Boltzmann-weight integrability and normalization
  needed for the interacting measure.

Everything downstream depends on that analytic core.
