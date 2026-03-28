/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.ShellEstimates
import Phi4.Interaction.NelsonBound

/-!
# Analytic Inputs for the Interaction Integrability

This file is now the thin orchestrator for the WP1 endpoint. The common UV
infrastructure lives in `Interaction/UVInfra`, the shell/L² convergence branch
lives in `Interaction/ShellEstimates`, and the negative-exponential Nelson
branch lives in `Interaction/NelsonBound`.
-/

noncomputable section

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal

/-! ## Closing gap_hasExpInteractionLp

The WP1 endpoint `HasExpInteractionLp` (i.e., exp(-V_Λ) ∈ Lᵖ for all finite p)
is proved by Fatou's lemma applied to the cutoff approximations:

1. From `gap_interactionCutoff_standardSeq_ae_convergence`:
   V_{Λ,κ_n} → V_Λ a.e. along the canonical sequence, hence
   exp(-p V_{Λ,κ_n}) → exp(-p V_Λ) a.e. (continuity of exp).
2. From `gap_exp_neg_interaction_uniform_bound`: E[exp(-p V_{Λ,κ})] ≤ C
   uniformly in κ (Nelson's bound).
3. Fatou: ∫⁻ exp(-pV_Λ) ≤ liminf ∫⁻ exp(-pV_{Λ,κ_n}) ≤ C < ⊤.
4. AEStronglyMeasurable + finite eLpNorm → MemLp.

This route bypasses Part2/Part3 entirely and needs only two analytic inputs:
`gap_interactionCutoff_standardSeq_ae_convergence` and
`gap_exp_neg_interaction_uniform_bound`. -/

/-- The Chapter 8 interaction integrability core: exp(-V_Λ) ∈ Lᵖ for all p < ∞.
    Proved by Fatou's lemma: Nelson's uniform negative exponential moment bounds
    on the cutoff interactions plus a.e. convergence give MemLp for the limit. -/
theorem gap_hasExpInteractionLp (params : Phi4Params) :
    HasExpInteractionLp params := by
  intro Λ (p : ℝ≥0∞) hp_ne_top
  set μ := freeFieldMeasure params.mass params.mass_pos
  -- Case p = 0: MemLp f 0 μ ↔ AEStronglyMeasurable f μ
  by_cases hp0 : p = 0
  · rw [hp0, memLp_zero_iff_aestronglyMeasurable]
    exact ((interaction_aestronglyMeasurable params Λ).aemeasurable.neg.exp).aestronglyMeasurable
  -- Case 0 < p < ⊤: use the Fatou bridge from Part1Core
  have hp_toReal_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp_ne_top
  -- a.e. convergence along standardUVCutoffSeq(n), then shift to (n+1)
  have hae_discrete :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop (nhds (interaction params Λ ω)) :=
    gap_interactionCutoff_standardSeq_ae_convergence params Λ
  have hae_shifted :
      ∀ᵐ ω ∂μ, Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
        Filter.atTop (nhds (interaction params Λ ω)) := by
    filter_upwards [hae_discrete] with ω hω
    exact hω.comp (Filter.tendsto_add_atTop_nat 1)
  -- Cutoff measurability for the shifted sequence
  have hcutoff_meas : ∀ n : ℕ,
      AEStronglyMeasurable
        (fun ω : FieldConfig2D => interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
        μ := by
    intro n
    exact (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq (n + 1))).aestronglyMeasurable
  -- Uniform lintegral bound from gap_exp_neg_interaction_uniform_bound (Nelson's bound)
  have hbound :
      ∃ C : ℝ≥0∞, C ≠ ⊤ ∧
        ∀ n : ℕ,
          ∫⁻ ω,
              ENNReal.ofReal
                (Real.exp (-(p.toReal * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
            ∂μ ≤ C := by
    obtain ⟨D, hD_pos, hD_bound⟩ :=
      gap_exp_neg_interaction_uniform_bound params Λ p.toReal hp_toReal_pos
    apply uniform_lintegral_bound_of_standardSeq_succ_uniform_integral_bound params Λ p.toReal
    exact ⟨D, fun n => (hD_bound (standardUVCutoffSeq (n + 1))).1,
           fun n => (hD_bound (standardUVCutoffSeq (n + 1))).2⟩
  -- Apply the Fatou bridge
  exact memLp_exp_neg_interaction_of_standardSeq_succ_tendsto_ae_of_uniform_lintegral_bound
    params Λ hp0 hp_ne_top hae_shifted hcutoff_meas hbound

end
