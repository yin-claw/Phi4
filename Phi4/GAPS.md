# Phi4 Proof-Gap Ledger

Date: 2026-03-06

This file records the current proof boundary on `main`.

## Trust Snapshot

- theorem-level `sorry` in core modules: `18`
- legacy `class/structure .*Model`: `13`
- canonical `gap_*` theorem frontiers: `33`
- `axiom`: `0`
- `def/abbrev := by sorry`: `0`

So the project has no hidden axiom-style placeholders, but it is still far from
assumption-free completion. The open mathematics is currently split between:

1. explicit theorem-level frontier statements, and
2. a reduced but still substantial legacy `...Model` assumption surface.

## Canonical `gap_*` Theorem Surface

Not every `gap_*` theorem below is still open. Some are now closed support
theorems that remain as canonical named endpoints. The active proof boundary is
tracked by the theorem-level `sorry` count above.

### WP0: Free/Gaussian combinatorial bridge
1. `gap_pairing_card`
2. `gap_wicks_theorem_even`
3. `gap_feynman_graph_expansion`
4. `gap_localized_graph_exponential_decay`
5. `gap_covariance_eq_kernel`

### WP1: Finite-volume integrability (CRITICAL PATH)
6. `gap_uvMollifier_continuous` — UV mollifier continuity `[closed]`
7. `gap_interactionCutoff_sq_integrable` — L² integrability of cutoff interaction `[closed]`
8. `gap_interactionCutoff_standardSeq_L2_increment_rate` — L² rate bound on UV increments
9. `gap_interactionCutoff_standardSeq_summable_L1_increments` — summable L¹ increments `[closed modulo 8]`
10. `gap_interactionCutoff_standardSeq_ae_convergence` — **sequence-level a.e. convergence (on critical path)** `[closed modulo 8]`
11. `gap_interaction_double_exponential_tail_bound` — Nelson's double-exponential tail
12. `gap_exp_neg_interaction_uniform_bound` — **Nelson's uniform bound (on critical path)** `[closed modulo 11]`
13. `gap_hasExpInteractionLp` — WP1 endpoint

#### WP1 non-critical (retained for completeness, not on main path)
14. `gap_interactionCutoff_L2_convergence` — continuous-parameter L² convergence
15. `gap_interactionCutoff_ae_convergence` — continuous-parameter a.e. convergence
16. `gap_interaction_aestronglyMeasurable` — measurability of limiting interaction `[closed]`
17. `gap_interaction_sq_integrable` — square-integrability of the limiting interaction `[closed]`

### WP2: Finite-volume monotonicity, comparison, reflection positivity
18. `gap_schwingerTwo_le_free`
19. `gap_hasSchwingerNMonotone`
20. `gap_hasChessboardEstimate`
21. `gap_hasSchwingerUniformBound`
22. `gap_free_covariance_reflection_positive`
23. `gap_dirichlet_covariance_reflection_positive`
24. `gap_interacting_measure_reflection_positive`

### WP3: Infinite-volume limit
25. `gap_infiniteVolumeLimit_exists`

### WP4: Regularity and equation of motion
26. `gap_wick_powers_infinite_volume`
27. `gap_wickCubicSmeared_tendsto_ae`
28. `gap_euclidean_equation_of_motion`
29. `gap_generating_functional_bound`
30. `gap_generating_functional_bound_uniform`
31. `gap_nonlocal_phi4_bound`

### WP5: OS packaging and reconstruction
32. `gap_measure_os3_reflection_positive`
33. `gap_phi4_linear_growth`

## WP1 Critical Path

The WP1 endpoint `hasExpInteractionLp_of_analytic_inputs` needs exactly:

```
gap_interactionCutoff_standardSeq_L2_increment_rate
  → gap_interactionCutoff_standardSeq_summable_L1_increments
    → gap_interactionCutoff_standardSeq_ae_convergence  (PROVED modulo L1 summability)

gap_interaction_double_exponential_tail_bound
  + neg_exp_moment_of_double_exponential_tail (internal helper, PROVED)
  + integral_exp_linear_minus_double_exp_finite (internal helper, PROVED)
    → gap_exp_neg_interaction_uniform_bound  (PROVED modulo sub-lemmas)

Both → hasExpInteractionLp_of_analytic_inputs  (PROVED modulo above)
```

Recent quantitative infrastructure on the shell branch:
- `wickPower_four_step_decomposition`
- `rawFieldEval_sub_sq_expectation`
- `rawFieldEval_sub_fourth_expectation`

These reduce `gap_interactionCutoff_standardSeq_L2_increment_rate` to the
remaining covariance-shell and polynomial-moment estimates, rather than to
further algebraic manipulation of the quartic Wick increment.

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
  needed for the interacting measure, together with the newly surfaced
  analytic-input obligations in `Interaction/AnalyticInputs.lean`.

Everything downstream depends on that analytic core.
