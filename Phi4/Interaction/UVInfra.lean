/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part3
import Mathlib.Analysis.Convex.Integral
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# UV and Measurability Infrastructure for Interaction Analytic Inputs

This file contains the common UV-cutoff, measurability, compact-moment, and
basic `L²` infrastructure shared by the shell-convergence and Nelson-bound
branches of the interaction analysis.
-/

noncomputable section

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal

/-! ## Frontier: UV mollifier continuity in spacetime

The UV mollifier δ_{κ,x} varies continuously in x in the Schwartz topology.
This is because translation is a continuous operation on S(ℝ²). -/

/-- The ContDiffBump underlying the UV mollifier. -/
private def uvBump (κ : UVCutoff) (x : Spacetime2D) : ContDiffBump x :=
  ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹, inv_pos.mpr (mul_pos two_pos κ.hκ),
   by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩

/-- The iterated derivative of the base mollifier vanishes outside the support ball. -/
private lemma iteratedFDeriv_uvMollifier_zero_outside (κ : UVCutoff) (n : ℕ)
    (z : Spacetime2D) (hz : ‖z‖ > κ.κ⁻¹) :
    iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) z = 0 := by
  apply image_eq_zero_of_notMem_tsupport; intro hmem
  have : z ∈ Metric.closedBall (0 : Spacetime2D) κ.κ⁻¹ :=
    (tsupport_iteratedFDeriv_subset (𝕜 := ℝ) (f := (uvMollifier κ 0 : Spacetime2D → ℝ)) n).trans
      (by simpa using (tsupport_uvMollifier_eq κ (0 : Spacetime2D)).le) hmem
  rw [Metric.mem_closedBall, dist_zero_right] at this; linarith

/-- Translation identity for the iterated derivative of the UV mollifier. -/
private lemma iteratedFDeriv_uvMollifier_translate (κ : UVCutoff) (n : ℕ) (a y : Spacetime2D) :
    iteratedFDeriv ℝ n (⇑(uvMollifier κ a)) y =
    iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - a) := by
  show iteratedFDeriv ℝ n (uvMollifier κ a).toFun y =
    iteratedFDeriv ℝ n (uvMollifier κ 0).toFun (y - a)
  have : (uvMollifier κ a).toFun = fun z => (uvMollifier κ 0).toFun (z - a) := by
    ext z
    simpa using uvMollifier_apply_sub κ a z
  rw [this, iteratedFDeriv_comp_sub]

/-- The iterated derivative of a difference of Schwartz maps equals the difference
    of iterated derivatives. -/
private lemma iteratedFDeriv_sub_schwartz (f g : SchwartzMap Spacetime2D ℝ)
    (n : ℕ) (y : Spacetime2D) :
    iteratedFDeriv ℝ n (⇑(f - g)) y =
    iteratedFDeriv ℝ n (⇑f) y - iteratedFDeriv ℝ n (⇑g) y := by
  show iteratedFDeriv ℝ n (f - g).toFun y =
    iteratedFDeriv ℝ n f.toFun y - iteratedFDeriv ℝ n g.toFun y
  have hfeq : (f - g).toFun = fun z => f.toFun z + (-g.toFun z) := by
    ext z; show f z - g z = f z + (-(g z)); ring
  rw [hfeq, iteratedFDeriv_add_apply'
    (f.smooth'.of_le (by exact_mod_cast le_top)).contDiffAt
    (g.smooth'.of_le (by exact_mod_cast le_top)).contDiffAt.neg]
  have : (fun x => -g.toFun x) = -g.toFun := by ext; simp
  rw [this, iteratedFDeriv_neg_apply]; abel

/-- The UV mollifier is continuous as a function of the spacetime point in the
    Schwartz topology: x ↦ uvMollifier κ x is continuous as Spacetime2D → TestFun2D.
    This holds because translation is continuous in the Schwartz topology. -/
theorem uvMollifier_continuous (κ : UVCutoff) :
    Continuous (fun x : Spacetime2D => uvMollifier κ x) := by
  rw [continuous_iff_continuousAt]; intro x₀
  rw [ContinuousAt, (schwartz_withSeminorms ℝ Spacetime2D ℝ).tendsto_nhds]
  intro ⟨k, n⟩ ε hε
  simp only [SchwartzMap.schwartzSeminormFamily_apply]
  set R := κ.κ⁻¹
  have hR_pos : 0 < R := inv_pos.mpr κ.hκ
  -- The base iterated derivative is uniformly continuous (compactly supported + smooth)
  have hD_uc : UniformContinuous
      (iteratedFDeriv ℝ n (⇑(uvMollifier κ 0) : Spacetime2D → ℝ)) := by
    apply HasCompactSupport.uniformContinuous_of_continuous
    · have huv_hc : HasCompactSupport (fun z : Spacetime2D => uvMollifier κ 0 z) := by
        rw [HasCompactSupport, tsupport_uvMollifier_eq]
        exact isCompact_closedBall (x := (0 : Spacetime2D)) (r := κ.κ⁻¹)
      exact huv_hc.iteratedFDeriv n
    · exact ((uvMollifier κ 0).smooth').continuous_iteratedFDeriv (by exact_mod_cast le_top)
  -- Bound: on the support region, ‖y‖ ≤ ‖x₀‖ + R + 1
  have hbase_nn : 0 ≤ ‖x₀‖ + R + 1 := by linarith [norm_nonneg x₀]
  set B := (‖x₀‖ + R + 1) ^ k
  have hB_nn : 0 ≤ B := pow_nonneg hbase_nn k
  set ε' := ε / (B + 1)
  have hε'_pos : 0 < ε' := div_pos hε (by linarith)
  -- From uniform continuity, get δ₁ controlling the derivative difference
  obtain ⟨δ₁, hδ₁_pos, hδ₁⟩ := (Metric.uniformContinuous_iff.mp hD_uc) ε' hε'_pos
  rw [Metric.eventually_nhds_iff]
  refine ⟨min δ₁ 1, lt_min hδ₁_pos one_pos, fun x hx => ?_⟩
  have hx1 : dist x x₀ < 1 := lt_of_lt_of_le hx (min_le_right _ _)
  have hxδ₁ : dist x x₀ < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  -- Bound the Schwartz seminorm by B * ε' using seminorm_le_bound, then show B * ε' < ε
  apply lt_of_le_of_lt
    (SchwartzMap.seminorm_le_bound ℝ k n _ (mul_nonneg hB_nn (le_of_lt hε'_pos)) _)
  · calc B * ε' = ε * B / (B + 1) := by ring
      _ < ε * (B + 1) / (B + 1) := div_lt_div_of_pos_right
          (mul_lt_mul_of_pos_left (by linarith) hε) (by linarith)
      _ = ε := by field_simp
  · -- Pointwise bound: ‖y‖^k * ‖iteratedFDeriv ℝ n (uvMol x - uvMol x₀) y‖ ≤ B * ε'
    intro y
    rw [iteratedFDeriv_sub_schwartz,
        iteratedFDeriv_uvMollifier_translate κ n x y,
        iteratedFDeriv_uvMollifier_translate κ n x₀ y]
    by_cases hy : dist y x₀ ≤ R + 1
    · -- y in support region: ‖y‖ bounded, use uniform continuity
      have hy_norm : ‖y‖ ≤ ‖x₀‖ + R + 1 := by
        have h := norm_add_le (y - x₀) x₀; rw [sub_add_cancel] at h
        linarith [show ‖y - x₀‖ ≤ R + 1 from by rwa [← dist_eq_norm]]
      have hD_close : ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
          iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖ < ε' := by
        rw [← dist_eq_norm]; apply hδ₁
        rw [dist_eq_norm, show (y - x) - (y - x₀) = x₀ - x from by abel, norm_sub_rev]
        exact dist_eq_norm x x₀ ▸ hxδ₁
      calc ‖y‖ ^ k * ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
              iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖
          ≤ B * ‖iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x) -
              iteratedFDeriv ℝ n (⇑(uvMollifier κ 0)) (y - x₀)‖ :=
            mul_le_mul_of_nonneg_right
              (pow_le_pow_left₀ (norm_nonneg _) hy_norm k) (norm_nonneg _)
        _ ≤ B * ε' := mul_le_mul_of_nonneg_left (le_of_lt hD_close) hB_nn
    · -- y outside support region: both D values vanish
      push_neg at hy
      have hy_x : ‖y - x‖ > R := by
        calc R < dist y x₀ - dist x x₀ := by linarith
          _ ≤ dist y x := by linarith [dist_triangle y x x₀]
          _ = ‖y - x‖ := dist_eq_norm y x
      have hy_x₀ : ‖y - x₀‖ > R := by rw [← dist_eq_norm]; linarith
      rw [iteratedFDeriv_uvMollifier_zero_outside κ n _ hy_x,
          iteratedFDeriv_uvMollifier_zero_outside κ n _ hy_x₀,
          sub_self, norm_zero, mul_zero]
      exact mul_nonneg hB_nn (le_of_lt hε'_pos)

/-- Continuity of a covariance pairing along continuous test-function families. -/
theorem continuous_covariance_comp
    (T : TestFun2D →L[ℝ] GaussianField.ell2')
    {u v : Spacetime2D → TestFun2D}
    (hu : Continuous u) (hv : Continuous v) :
    Continuous fun x : Spacetime2D => GaussianField.covariance T (u x) (v x) := by
  simpa [GaussianField.covariance] using (T.continuous.comp hu).inner (T.continuous.comp hv)

/-- On compact sets, continuous covariance pairings of continuous test-function
families are uniformly bounded in absolute value. -/
theorem covariance_comp_abs_bounded_on_compact
    (T : TestFun2D →L[ℝ] GaussianField.ell2')
    {u v : Spacetime2D → TestFun2D}
    (hu : Continuous u) (hv : Continuous v)
    (K : Set Spacetime2D) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ K, |GaussianField.covariance T (u x) (v x)| ≤ M := by
  obtain ⟨M0, hM0⟩ := hK.exists_bound_of_continuousOn
    ((continuous_covariance_comp T hu hv).abs).continuousOn
  refine ⟨max M0 0, le_max_right _ _, fun x hx => ?_⟩
  have hbound : |GaussianField.covariance T (u x) (v x)| ≤ M0 := by
    simpa [Real.norm_eq_abs, abs_of_nonneg (abs_nonneg _)] using hM0 x hx
  exact hbound.trans (le_max_left _ _)

/-- Specialization of compact covariance bounds to translated UV mollifiers. -/
theorem uvMollifier_covariance_abs_bounded_on_compact
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff)
    (K : Set Spacetime2D) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ x ∈ K,
        |GaussianField.covariance (freeCovarianceCLM mass hmass)
            (uvMollifier κ₁ x) (uvMollifier κ₂ x)| ≤ M := by
  exact covariance_comp_abs_bounded_on_compact
    (T := freeCovarianceCLM mass hmass)
    (uvMollifier_continuous κ₁) (uvMollifier_continuous κ₂) K hK

/-- Self-covariances of the CLM are nonnegative. -/
theorem covariance_self_nonneg
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    0 ≤ GaussianField.covariance (freeCovarianceCLM mass hmass) f f := by
  change 0 ≤ @inner ℝ ↥ell2' _ ((freeCovarianceCLM mass hmass) f) ((freeCovarianceCLM mass hmass) f)
  rw [real_inner_self_eq_norm_sq]
  positivity

/-- Covariances satisfy the real Cauchy-Schwarz inequality. -/
theorem covariance_sq_le_self_mul_self
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2 ≤
      GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
        GaussianField.covariance (freeCovarianceCLM mass hmass) g g := by
  simpa [GaussianField.covariance, sq] using
    (real_inner_mul_inner_self_le
      ((freeCovarianceCLM mass hmass) f) ((freeCovarianceCLM mass hmass) g))

/-! ## Measurability of field evaluations and Wick products -/

/-- The raw field evaluation is strongly measurable in ω for each fixed spacetime point. -/
theorem rawFieldEval_stronglyMeasurable (mass : ℝ) (κ : UVCutoff) (x : Spacetime2D) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (fun ω => rawFieldEval mass κ ω x) :=
  (continuous_id.stronglyMeasurable).comp_measurable
    (configuration_eval_measurable (uvMollifier κ x))

/-- Wick power is strongly measurable in ω for each fixed spacetime point. -/
theorem wickPower_stronglyMeasurable (n : ℕ) (mass : ℝ) (κ : UVCutoff) (x : Spacetime2D) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (fun ω => wickPower n mass κ ω x) := by
  unfold wickPower rawFieldEval
  exact (wickMonomial_continuous n (regularizedPointCovariance mass κ)).stronglyMeasurable.comp_measurable
    (configuration_eval_measurable (uvMollifier κ x))

/-- The raw field evaluation is continuous in x for each fixed ω.
    This follows from continuity of the UV mollifier and continuity of ω. -/
theorem rawFieldEval_continuous_in_x (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) :
    Continuous (fun x : Spacetime2D => rawFieldEval mass κ ω x) := by
  unfold rawFieldEval
  exact ω.continuous.comp (uvMollifier_continuous κ)

/-- Wick power is continuous in x for each fixed ω. -/
theorem wickPower_continuous_in_x (n : ℕ) (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D) :
    Continuous (fun x : Spacetime2D => wickPower n mass κ ω x) := by
  unfold wickPower rawFieldEval
  exact (wickMonomial_continuous n _).comp (ω.continuous.comp (uvMollifier_continuous κ))

/-- Joint strong measurability of the Wick power on FieldConfig2D × Spacetime2D.
    Uses the Carathéodory condition: measurable in ω for each x, continuous in x for each ω.
    Requires SecondCountableTopology on Spacetime2D (which holds for ℝ²). -/
theorem wickPower_stronglyMeasurable_uncurry (n : ℕ) (mass : ℝ) (κ : UVCutoff) :
    @StronglyMeasurable (FieldConfig2D × Spacetime2D) ℝ _
      (instMeasurableSpaceConfiguration.prod inferInstance)
      (Function.uncurry (fun ω x => wickPower n mass κ ω x)) := by
  -- Use stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
  -- with ι = Spacetime2D, α = FieldConfig2D, u x ω = wickPower n mass κ ω x
  -- giving uncurry u : Spacetime2D × FieldConfig2D → ℝ, then swap
  letI : MeasurableSpace FieldConfig2D := instMeasurableSpaceConfiguration
  have hjoint :=
    @stronglyMeasurable_uncurry_of_continuous_of_stronglyMeasurable
      FieldConfig2D ℝ Spacetime2D
      _ _ _ _ _ _ _ instMeasurableSpaceConfiguration
      (fun x ω => wickPower n mass κ ω x)
      (fun ω => wickPower_continuous_in_x n mass κ ω)
      (fun x => wickPower_stronglyMeasurable n mass κ x)
  -- hjoint : StronglyMeasurable (uncurry (fun x ω => ...)) on (Spacetime2D × FieldConfig2D)
  -- Swap to get (FieldConfig2D × Spacetime2D)
  convert hjoint.comp_measurable measurable_swap using 1

/-! ## Measurability of the interaction -/

/-- The UV-cutoff interaction is strongly measurable as a function of ω. -/
theorem interactionCutoff_stronglyMeasurable (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) :
    @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
      (interactionCutoff params Λ κ) := by
  unfold interactionCutoff
  -- params.coupling * ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
  apply StronglyMeasurable.const_mul
  -- Need: ω ↦ ∫ x in Λ.toSet, wickPower 4 mass κ ω x is strongly measurable
  -- Use StronglyMeasurable.integral_prod_right with the joint measurability
  -- The set integral ∫ x in S, f x = ∫ x, S.indicator f x
  show StronglyMeasurable fun ω =>
    ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
  -- Rewrite set integral as full integral with indicator
  have h_eq : (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) =
      (fun ω => ∫ x, Λ.toSet.indicator (fun x => wickPower 4 params.mass κ ω x) x) := by
    ext ω; rw [integral_indicator Λ.toSet_measurableSet]
  rw [h_eq]
  -- Now use StronglyMeasurable.integral_prod_right
  -- We need StronglyMeasurable (uncurry (fun ω x => indicator ...)) on (FieldConfig2D × Spacetime2D)
  apply StronglyMeasurable.integral_prod_right
  -- Need: StronglyMeasurable (fun (ω, x) => Λ.toSet.indicator (wickPower 4 mass κ ω ·) x)
  -- This is StronglyMeasurable (fun (ω, x) => indicator Λ.toSet (wickPower 4 mass κ ω ·) x)
  -- = StronglyMeasurable of indicator of a jointly measurable function over a measurable set
  apply StronglyMeasurable.indicator
  · -- The function (ω, x) ↦ wickPower 4 mass κ ω x is jointly strongly measurable
    exact wickPower_stronglyMeasurable_uncurry 4 params.mass κ
  · -- {(ω, x) | x ∈ Λ.toSet} is measurable in the product
    exact Λ.toSet_measurableSet.preimage measurable_snd

/-- The UV-cutoff interaction is AEStronglyMeasurable under the free field measure. -/
theorem interactionCutoff_aestronglyMeasurable (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    AEStronglyMeasurable (interactionCutoff params Λ κ)
      (freeFieldMeasure params.mass params.mass_pos) :=
  (interactionCutoff_stronglyMeasurable params Λ κ).aestronglyMeasurable

/-! ## L² integrability of the cutoff interaction

The cutoff interaction V_{Λ,κ} = λ ∫_Λ :φ_κ(x)⁴: dx is a quadratic form in the
Gaussian field pairings ω(δ_{κ,x}). For fixed κ, all moments are finite because:
- Each ω(δ_{κ,x}) is Gaussian with variance c_κ
- :φ_κ(x)⁴: is a polynomial in ω(δ_{κ,x})
- Polynomials of Gaussians have all moments finite
- The integral over Λ (bounded region) preserves integrability

The proof uses:
1. wickPower_memLp: for each x, the Wick power is in L^p(dμ) for all finite p
2. Cauchy-Schwarz: (∫_Λ f dx)² ≤ vol(Λ) * ∫_Λ f² dx
3. Fubini-Tonelli: E[∫_Λ f² dx] = ∫_Λ E[f²] dx for f² ≥ 0
4. Translation invariance: E[:φ_κ(x)⁴:²] is constant in x
-/

/-- For each fixed spacetime point, the square of the Wick power is integrable
    under the free field measure. Immediate from `wickPower_memLp` with p = 2. -/
theorem wickPower_sq_integrable (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (x : Spacetime2D) :
    Integrable (fun ω => (wickPower 4 mass κ ω x) ^ 2)
      (freeFieldMeasure mass hmass) :=
  (wickPower_memLp 4 mass hmass κ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)).integrable_sq

/-- At a fixed spacetime point, the difference of two quartic Wick powers has
all finite even moments. This is a local Gaussian-polynomial fact, separate
from the genuinely hard spatial/UV comparison used later in the Nelson branch. -/
private theorem wickPower_sub_even_integrable
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff)
    (x : Spacetime2D) (j : ℕ) :
    Integrable
      (fun ω : FieldConfig2D =>
        |wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x| ^ (2 * j))
      (freeFieldMeasure mass hmass) := by
  let μ := freeFieldMeasure mass hmass
  let p : ℝ≥0∞ := ((2 * j : ℕ) : ℝ≥0∞)
  have hp_top : p ≠ ⊤ := by
    simpa [p] using (ENNReal.coe_ne_top : (((2 * j : ℕ) : ℝ≥0∞)) ≠ ⊤)
  have hmem :
      MemLp
        (fun ω : FieldConfig2D =>
          wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x)
        p μ := by
    exact
      (wickPower_memLp 4 mass hmass κ₂ x hp_top).sub
      (wickPower_memLp 4 mass hmass κ₁ x hp_top)
  have hnorm :
      Integrable
        (fun ω : FieldConfig2D =>
          ‖wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x‖ ^ p.toReal)
        μ := by
    simpa using hmem.integrable_norm_rpow'
  refine hnorm.congr ?_
  filter_upwards with ω
  rw [show p.toReal = ((2 * j : ℕ) : ℝ) by simp [p], Real.rpow_natCast]
  simp [Real.norm_eq_abs]

/-- Cauchy-Schwarz for set integrals over a finite-measure set:
    (∫ x in S, f x)² ≤ (μ S).toReal * ∫ x in S, f x ^ 2.
    This is Jensen's inequality for the convex function (·)². -/
theorem sq_setIntegral_le_volume_mul_setIntegral_sq {f : Spacetime2D → ℝ}
    (S : Set Spacetime2D) (_hS : MeasurableSet S)
    (hfint : Integrable f (MeasureTheory.volume.restrict S))
    (hf2int : Integrable (fun x => f x ^ 2) (MeasureTheory.volume.restrict S))
    (hvol : MeasureTheory.volume S ≠ ⊤) :
    (∫ x in S, f x) ^ 2 ≤
      (MeasureTheory.volume S).toReal * ∫ x in S, f x ^ 2 := by
  -- If vol(S) = 0, both sides are 0
  by_cases hvol0 : MeasureTheory.volume S = 0
  · have hrestr : MeasureTheory.volume.restrict S = 0 :=
      MeasureTheory.Measure.restrict_eq_zero.mpr hvol0
    simp [hrestr]
  -- vol(S) > 0: use Jensen's inequality for (·)²
  have hconv : ConvexOn ℝ Set.univ (fun x : ℝ => x ^ 2) :=
    Even.convexOn_pow ⟨1, rfl⟩
  have hjensen := ConvexOn.map_set_average_le hconv
    (continuous_pow 2 |>.continuousOn) isClosed_univ
    hvol0 hvol (by simp) hfint hf2int
  -- hjensen : (⨍ x in S, f x) ^ 2 ≤ ⨍ x in S, f x ^ 2
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hjensen
  simp only [smul_eq_mul, MeasureTheory.Measure.real] at hjensen
  rw [mul_pow] at hjensen
  -- hjensen : V⁻¹ ^ 2 * (∫_S f) ^ 2 ≤ V⁻¹ * ∫_S f²  where V = (volume S).toReal
  have hVpos : 0 < (MeasureTheory.volume S).toReal := ENNReal.toReal_pos hvol0 hvol
  -- Multiply both sides by V² to clear denominators
  have h1 := mul_le_mul_of_nonneg_left hjensen
    (sq_nonneg (MeasureTheory.volume S).toReal)
  set V := (MeasureTheory.volume S).toReal with hV_def
  have hVne : V ≠ 0 := hVpos.ne'
  have hVinv_pos : 0 < V⁻¹ := inv_pos.mpr hVpos
  -- hjensen: V⁻¹ ^ 2 * (∫ f)² ≤ V⁻¹ * ∫ f²
  -- Rewrite V⁻¹ ^ 2 = V⁻¹ * V⁻¹ and reassociate
  rw [sq, mul_assoc] at hjensen
  -- hjensen: V⁻¹ * (V⁻¹ * (∫ f)²) ≤ V⁻¹ * ∫ f²
  -- Cancel V⁻¹ from both sides (V⁻¹ > 0)
  have h1 := le_of_mul_le_mul_left hjensen hVinv_pos
  -- h1: V⁻¹ * (∫ f)² ≤ ∫ f²
  -- Multiply both sides by V (> 0)
  have h2 := mul_le_mul_of_nonneg_left h1 hVpos.le
  -- h2: V * (V⁻¹ * (∫ f)²) ≤ V * ∫ f²
  rw [← mul_assoc, mul_inv_cancel₀ hVne, one_mul] at h2
  -- h2: (∫ f)² ≤ V * ∫ f²
  exact h2

/-- Jensen/Hölder bound for higher moments on a finite-volume set:
    `|∫_S f|^n ≤ vol(S)^(n-1) * ∫_S |f|^n` for `n ≥ 1`. -/
theorem abs_setIntegral_pow_le_volume_pow_mul_setIntegral_abs_pow
    {f : Spacetime2D → ℝ}
    (S : Set Spacetime2D) (_hS : MeasurableSet S)
    (n : ℕ) (hn : 0 < n)
    (hfint : Integrable f (MeasureTheory.volume.restrict S))
    (hfnint : Integrable (fun x => |f x| ^ n) (MeasureTheory.volume.restrict S))
    (hvol : MeasureTheory.volume S ≠ ⊤) :
    |∫ x in S, f x| ^ n ≤
      (MeasureTheory.volume S).toReal ^ (n - 1) * ∫ x in S, |f x| ^ n := by
  by_cases hvol0 : MeasureTheory.volume S = 0
  · have hrestr : MeasureTheory.volume.restrict S = 0 :=
      MeasureTheory.Measure.restrict_eq_zero.mpr hvol0
    simp [hrestr, hn.ne']
  have hconv : ConvexOn ℝ (Set.Ici (0 : ℝ)) (fun x : ℝ => x ^ n) := convexOn_pow n
  have hcont : ContinuousOn (fun x : ℝ => x ^ n) (Set.Ici (0 : ℝ)) :=
    (continuous_pow n).continuousOn
  have hclosed : IsClosed (Set.Ici (0 : ℝ)) := isClosed_Ici
  have hae_nonneg : ∀ᵐ x ∂(MeasureTheory.volume.restrict S), |f x| ∈ Set.Ici (0 : ℝ) := by
    filter_upwards with x
    exact Set.mem_Ici.mpr (abs_nonneg _)
  have hfabs : Integrable (fun x => |f x|) (MeasureTheory.volume.restrict S) := hfint.abs
  have hjensen := ConvexOn.map_set_average_le hconv hcont hclosed
    hvol0 hvol hae_nonneg hfabs hfnint
  rw [MeasureTheory.setAverage_eq, MeasureTheory.setAverage_eq] at hjensen
  simp only [smul_eq_mul, MeasureTheory.Measure.real] at hjensen
  rw [mul_pow] at hjensen
  set V := (MeasureTheory.volume S).toReal with hV_def
  have hVpos : 0 < V := by
    rw [hV_def]
    exact ENNReal.toReal_pos hvol0 hvol
  have hVne : V ≠ 0 := hVpos.ne'
  have hVinv_pos : 0 < V⁻¹ := inv_pos.mpr hVpos
  have hmean :
      (∫ x in S, |f x|) ^ n ≤ V ^ (n - 1) * ∫ x in S, |f x| ^ n := by
    have hcancel1 :
        (V⁻¹) ^ (n - 1) * (∫ x in S, |f x|) ^ n ≤ ∫ x in S, |f x| ^ n := by
      have hrew :
          (V⁻¹) ^ n * (∫ x in S, |f x|) ^ n =
            V⁻¹ * ((V⁻¹) ^ (n - 1) * (∫ x in S, |f x|) ^ n) := by
        cases n with
        | zero =>
            cases (Nat.not_lt_zero _ hn)
        | succ m =>
            simp [pow_succ, mul_assoc, mul_left_comm, mul_comm]
      rw [hrew] at hjensen
      exact le_of_mul_le_mul_left
        (show V⁻¹ * ((V⁻¹) ^ (n - 1) * (∫ x in S, |f x|) ^ n) ≤
            V⁻¹ * ∫ x in S, |f x| ^ n from hjensen)
        hVinv_pos
    cases n with
    | zero =>
        cases (Nat.not_lt_zero _ hn)
    | succ m =>
        have hscaled :=
            mul_le_mul_of_nonneg_left hcancel1 (pow_nonneg hVpos.le m)
        simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm, hVne] using hscaled
  have habs :
      |∫ x in S, f x| ≤ ∫ x in S, |f x| := by
    simpa using
      (MeasureTheory.abs_integral_le_integral_abs
        (μ := MeasureTheory.volume.restrict S) (f := f))
  have hpow_abs :
      |∫ x in S, f x| ^ n ≤ (∫ x in S, |f x|) ^ n :=
    pow_le_pow_left₀ (abs_nonneg _) habs n
  exact le_trans hpow_abs hmean

/-- If the pointwise difference of two cutoff Wick powers has integrable `2j`-th
moment on the product space `μ × ν`, then the cutoff interaction difference has
integrable `2j`-th moment under `μ`. This isolates the spatial Jensen/Fubini
step from the genuinely hard Gaussian-moment comparison used later in the
Nelson branch. -/
private theorem interactionCutoff_sub_even_integrable_of_prod
    (params : Phi4Params) (Λ : Rectangle) (κ₁ κ₂ : UVCutoff)
    (j : ℕ) (hj : 0 < j)
    (hprod :
      Integrable
        (fun p : FieldConfig2D × Spacetime2D =>
          |wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j))
        ((freeFieldMeasure params.mass params.mass_pos).prod
          (MeasureTheory.volume.restrict Λ.toSet))) :
    Integrable
      (fun ω : FieldConfig2D =>
        |interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω| ^ (2 * j))
      (freeFieldMeasure params.mass params.mass_pos) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  let d : FieldConfig2D → Spacetime2D → ℝ :=
    fun ω x => wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x
  have hfub :
      Integrable (fun ω => ∫ x, |d ω x| ^ (2 * j) ∂ν) μ := by
    simpa [μ, ν, d] using hprod.integral_prod_left
  have hdom :
      Integrable
        (fun ω =>
          |params.coupling| ^ (2 * j) *
            (MeasureTheory.volume Λ.toSet).toReal ^ (2 * j - 1) *
            ∫ x, |d ω x| ^ (2 * j) ∂ν)
        μ := by
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (hfub.const_mul ((MeasureTheory.volume Λ.toSet).toReal ^ (2 * j - 1))).const_mul
        (|params.coupling| ^ (2 * j))
  apply hdom.mono
  · have hmeas :
        StronglyMeasurable
          (fun ω : FieldConfig2D =>
            interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) :=
      (interactionCutoff_stronglyMeasurable params Λ κ₂).sub
        (interactionCutoff_stronglyMeasurable params Λ κ₁)
    exact (hmeas.norm.pow _).aestronglyMeasurable
  · filter_upwards with ω
    have hpow_int :
        |∫ x in Λ.toSet, d ω x| ^ (2 * j) ≤
          (MeasureTheory.volume Λ.toSet).toReal ^ (2 * j - 1) *
            ∫ x in Λ.toSet, |d ω x| ^ (2 * j) := by
      apply abs_setIntegral_pow_le_volume_pow_mul_setIntegral_abs_pow
      · exact Λ.toSet_measurableSet
      · exact Nat.mul_pos (by norm_num) hj
      · exact ((wickPower_continuous_in_x 4 params.mass κ₂ ω).sub
          (wickPower_continuous_in_x 4 params.mass κ₁ ω)).continuousOn.integrableOn_compact
          Λ.toSet_isCompact
      · have hcont :
            Continuous (fun x : Spacetime2D => |d ω x| ^ (2 * j)) := by
          simpa [d, Real.norm_eq_abs] using
            (((wickPower_continuous_in_x 4 params.mass κ₂ ω).sub
              (wickPower_continuous_in_x 4 params.mass κ₁ ω)).norm.pow (2 * j))
        exact hcont.continuousOn.integrableOn_compact Λ.toSet_isCompact
      · exact Λ.toSet_volume_ne_top
    have hnonneg :
        0 ≤ |params.coupling| ^ (2 * j) := pow_nonneg (abs_nonneg _) _
    have hscaled := mul_le_mul_of_nonneg_left hpow_int hnonneg
    have hκ₂_int : Integrable (fun x => wickPower 4 params.mass κ₂ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₂ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hκ₁_int : Integrable (fun x => wickPower 4 params.mass κ₁ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₁ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hsub :
        interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω =
          params.coupling * ∫ x in Λ.toSet, d ω x := by
      rw [interactionCutoff, interactionCutoff, ← mul_sub, integral_sub hκ₂_int hκ₁_int]
    have hscaled' :
        (|params.coupling| * |∫ x in Λ.toSet, d ω x|) ^ (2 * j) ≤
          |params.coupling| ^ (2 * j) *
            (∫ x in Λ.toSet, |d ω x| ^ (2 * j)) * (MeasureTheory.volume Λ.toSet).toReal ^ (2 * j - 1) := by
      simpa [mul_pow, mul_assoc, mul_left_comm, mul_comm] using hscaled
    have hnonneg_int : 0 ≤ ∫ x in Λ.toSet, |d ω x| ^ (2 * j) := by
      exact integral_nonneg fun _ => by positivity
    have hscaled'' :
        (|params.coupling| * |∫ x in Λ.toSet, d ω x|) ^ (2 * j) ≤
          |params.coupling| ^ (2 * j) *
            |∫ x in Λ.toSet, |d ω x| ^ (2 * j)| * (MeasureTheory.volume Λ.toSet).toReal ^ (2 * j - 1) := by
      rw [abs_of_nonneg hnonneg_int]
      exact hscaled'
    simpa [ν, hsub, abs_mul, mul_assoc, mul_left_comm, mul_comm] using hscaled''

/-- Moment recursion: E[(ω f)^{n+2}] = (n+1) · Cov(f,f) · E[(ω f)^n].
    Re-derived from `wick_recursive` (the public Gaussian field API). -/
theorem moment_recursion_ai (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (n + 2) ∂(freeFieldMeasure mass hmass) =
    (↑(n + 1) : ℝ) * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, (ω f) ^ n ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass; set c := GaussianField.covariance T f f
  simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ (n + 2) = ω f * ∏ i : Fin (n + 1),
    ω ((fun _ : Fin (n + 1) => f) i) from fun ω => by
      rw [show (∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i)) = (ω f) ^ (n + 1) from
        Fin.prod_const (n + 1) (ω f)]; ring]
  change ∫ ω, ω f * ∏ i, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T n f (fun _ => f)]
  simp_rw [show @inner ℝ ell2' _ (T f) (T f) = c from rfl, Fin.prod_const]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  change _ = (↑(n + 1) : ℝ) * c * ∫ ω : Configuration TestFun2D, (ω f) ^ n ∂(measure T)
  push_cast; ring

/-- Powers of Gaussian pairings are integrable (from `product_integrable`). -/
theorem power_integrable_ai (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    Integrable (fun ω : FieldConfig2D => (ω f) ^ n) (freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ n = ∏ i : Fin n, ω ((fun _ => f) i) from
    fun ω => (Fin.prod_const n (ω f)).symm]
  change Integrable (fun ω => ∏ i : Fin n, ω ((fun _ => f) i)) (measure T)
  exact product_integrable T n (fun _ => f)

/-- Two-term power bound from Jensen/Chebyshev:
    `|a + b|^m ≤ 2^(m-1) (|a|^m + |b|^m)` for `m > 0`. -/
private theorem abs_add_pow_le_two_mul_sum_pow
    (a b : ℝ) {m : ℕ} (hm : 0 < m) :
    |a + b| ^ m ≤ 2 ^ (m - 1) * (|a| ^ m + |b| ^ m) := by
  have hsum :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin 2)))
      (f := fun i : Fin 2 => ![|a|, |b|] i)
      (by intro i hi; fin_cases i <;> simp)
      (m - 1)
  have h0 : |a + b| ≤ |a| + |b| := by
    simpa [Real.norm_eq_abs] using (norm_add_le a b)
  have hpow : |a + b| ^ m ≤ (|a| + |b|) ^ m := pow_le_pow_left₀ (abs_nonneg _) h0 m
  have hsum' : (|a| + |b|) ^ m ≤ 2 ^ (m - 1) * (|a| ^ m + |b| ^ m) := by
    have hm' : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    simpa [hm', Fin.sum_univ_two] using hsum
  exact le_trans hpow hsum'

/-- Three-term power bound from Jensen/Chebyshev:
    `|a + b + c|^m ≤ 3^(m-1) (|a|^m + |b|^m + |c|^m)` for `m > 0`. -/
private theorem abs_add_add_pow_le_three_mul_sum_pow
    (a b c : ℝ) {m : ℕ} (hm : 0 < m) :
    |a + b + c| ^ m ≤ 3 ^ (m - 1) * (|a| ^ m + |b| ^ m + |c| ^ m) := by
  have hsum :=
    pow_sum_le_card_mul_sum_pow
      (s := (Finset.univ : Finset (Fin 3)))
      (f := fun i : Fin 3 => ![|a|, |b|, |c|] i)
      (by intro i hi; fin_cases i <;> simp)
      (m - 1)
  have h0 : |a + b + c| ≤ |a| + |b| + |c| := by
    calc
      |a + b + c| = |(a + b) + c| := by ring_nf
      _ ≤ |a + b| + |c| := by simpa [Real.norm_eq_abs] using (norm_add_le (a + b) c)
      _ ≤ |a| + |b| + |c| := by
            gcongr
            simpa [Real.norm_eq_abs] using (norm_add_le a b)
  have hpow : |a + b + c| ^ m ≤ (|a| + |b| + |c|) ^ m := by
    exact pow_le_pow_left₀ (abs_nonneg _) h0 m
  have hsum' :
      (|a| + |b| + |c|) ^ m ≤ 3 ^ (m - 1) * (|a| ^ m + |b| ^ m + |c| ^ m) := by
    have hm' : m - 1 + 1 = m := Nat.succ_pred_eq_of_pos hm
    simpa [hm', Fin.sum_univ_three] using hsum
  exact le_trans hpow hsum'

/-- Uniform compact bound on even raw-field moments. The proof is a direct
Gaussian moment recursion using only compact covariance control. -/
private theorem rawField_even_moment_bounded_on_compact
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (K : Set Spacetime2D) (hK : IsCompact K) :
    ∀ n : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K,
      ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n)
        ∂(freeFieldMeasure mass hmass) ≤ M := by
  set T := freeCovarianceCLM mass hmass
  set μ := freeFieldMeasure mass hmass
  set covFun : Spacetime2D → ℝ := fun y =>
    GaussianField.covariance T (uvMollifier κ y) (uvMollifier κ y)
  obtain ⟨S, hSnn, hS⟩ := uvMollifier_covariance_abs_bounded_on_compact
    mass hmass κ κ K hK
  intro n
  induction n with
  | zero =>
      refine ⟨1, by positivity, ?_⟩
      intro y hy
      simp [rawFieldEval, μ]
  | succ n ihn =>
      rcases ihn with ⟨M, hMnn, hM⟩
      refine ⟨((↑(2 * n + 1) : ℝ) * S * M), by positivity, ?_⟩
      intro y hy
      set f : TestFun2D := uvMollifier κ y
      have hmoment :
          ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * (n + 1)) ∂μ =
            (↑(2 * n + 1) : ℝ) * covFun y *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ := by
        have hrec := moment_recursion_ai mass hmass f (2 * n)
        simpa [μ, covFun, rawFieldEval, T, f, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc,
          two_mul, add_comm, add_left_comm, add_assoc] using hrec
      have hI_nonneg :
          0 ≤ ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ := by
        exact integral_nonneg fun ω => by
          have hsq : 0 ≤ ((rawFieldEval mass κ ω y) ^ n) ^ 2 := sq_nonneg _
          simpa [pow_mul, Nat.mul_comm] using hsq
      have h1 :
          (↑(2 * n + 1) : ℝ) * covFun y *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ
            ≤
            (↑(2 * n + 1) : ℝ) * |covFun y| *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ := by
        have hcoeff :
            (↑(2 * n + 1) : ℝ) * covFun y ≤
              (↑(2 * n + 1) : ℝ) * |covFun y| := by
          exact mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity)
        exact mul_le_mul_of_nonneg_right hcoeff hI_nonneg
      have h2 :
          (↑(2 * n + 1) : ℝ) * |covFun y| *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ
            ≤
            (↑(2 * n + 1) : ℝ) * S * M := by
        have hleft :
            (↑(2 * n + 1) : ℝ) * |covFun y| ≤
              (↑(2 * n + 1) : ℝ) * S := by
          exact mul_le_mul_of_nonneg_left (hS y hy) (by positivity)
        calc
          (↑(2 * n + 1) : ℝ) * |covFun y| *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ
            ≤ ((↑(2 * n + 1) : ℝ) * S) * M := by
                exact mul_le_mul hleft (hM y hy) (by positivity) (by positivity)
          _ = (↑(2 * n + 1) : ℝ) * S * M := by ring
      calc
        ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * (n + 1)) ∂μ
          = (↑(2 * n + 1) : ℝ) * covFun y *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ := hmoment
        _ ≤ (↑(2 * n + 1) : ℝ) * |covFun y| *
              ∫ ω, (rawFieldEval mass κ ω y) ^ (2 * n) ∂μ := h1
        _ ≤ (↑(2 * n + 1) : ℝ) * S * M := h2

/-- Uniform compact bound on even moments of a quartic Wick field at a fixed
cutoff. This is a local Gaussian-polynomial fact and no longer part of the
hard Nelson frontier. -/
private theorem wickPower_even_moment_bounded_on_compact
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (K : Set Spacetime2D) (hK : IsCompact K)
    (j : ℕ) (hj : 0 < j) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K,
      ∫ ω, |wickPower 4 mass κ ω y| ^ (2 * j)
        ∂(freeFieldMeasure mass hmass) ≤ M := by
  let μ := freeFieldMeasure mass hmass
  let c₀ : ℝ := regularizedPointCovariance mass κ
  obtain ⟨M8, hM8nn, hM8⟩ := rawField_even_moment_bounded_on_compact
    mass hmass κ K hK (4 * j)
  obtain ⟨M4, hM4nn, hM4⟩ := rawField_even_moment_bounded_on_compact
    mass hmass κ K hK (2 * j)
  refine ⟨3 ^ (2 * j - 1) * (M8 + |6 * c₀| ^ (2 * j) * M4 + |3 * c₀ ^ 2| ^ (2 * j)),
    by positivity, ?_⟩
  intro y hy
  set X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω y
  let q : ℝ≥0∞ := ((2 * j : ℕ) : ℝ≥0∞)
  have hq_ne_top : q ≠ ⊤ := by
    exact ENNReal.coe_ne_top
  have hmem :
      MemLp (fun ω : FieldConfig2D => wickPower 4 mass κ ω y) q μ := by
    exact wickPower_memLp 4 mass hmass κ y hq_ne_top
  have hint :
      Integrable (fun ω : FieldConfig2D => |wickPower 4 mass κ ω y| ^ (2 * j)) μ := by
    have hint' :
        Integrable (fun ω : FieldConfig2D => |wickPower 4 mass κ ω y| ^ q.toReal) μ := by
      simpa [Real.norm_eq_abs] using hmem.integrable_norm_rpow'
    have hq_toReal : q.toReal = ((2 * j : ℕ) : ℝ) := by
      simp [q]
    convert hint' using 1
    ext ω
    rw [hq_toReal, Real.rpow_natCast]
  have hX8 : Integrable (fun ω : FieldConfig2D => (X ω) ^ (2 * (4 * j))) μ := by
    simpa [X, rawFieldEval] using power_integrable_ai mass hmass (uvMollifier κ y) (2 * (4 * j))
  have hX4 : Integrable (fun ω : FieldConfig2D => (X ω) ^ (2 * (2 * j))) μ := by
    simpa [X, rawFieldEval] using power_integrable_ai mass hmass (uvMollifier κ y) (2 * (2 * j))
  have hupper : Integrable
      (fun ω : FieldConfig2D =>
        3 ^ (2 * j - 1) *
          ((X ω) ^ (2 * (4 * j)) +
            |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)))
      μ := by
    have hupper0 :
        Integrable
          (fun ω : FieldConfig2D =>
            3 ^ (2 * j - 1) *
              ((X ω) ^ (2 * (4 * j)) +
                (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j))))
          μ := by
      exact ((hX8.add ((hX4.const_mul _).add (integrable_const _))).const_mul _)
    simpa [add_assoc, add_left_comm, add_comm, mul_assoc, mul_left_comm, mul_comm] using hupper0
  have hpoint :
      ∀ ω : FieldConfig2D,
        |wickPower 4 mass κ ω y| ^ (2 * j) ≤
          3 ^ (2 * j - 1) *
            ((X ω) ^ (2 * (4 * j)) + |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) +
              |3 * c₀ ^ 2| ^ (2 * j)) := by
    intro ω
    have hm2j : 0 < 2 * j := Nat.mul_pos (by norm_num) hj
    have hwick :
        wickPower 4 mass κ ω y =
          (X ω) ^ 4 + -(6 * c₀ * (X ω) ^ 2) + 3 * c₀ ^ 2 := by
      simp [wickPower, wickMonomial_four, X, c₀]
      ring
    have hpow :=
      abs_add_add_pow_le_three_mul_sum_pow
        ((X ω) ^ 4) (-(6 * c₀ * (X ω) ^ 2)) (3 * c₀ ^ 2)
        hm2j
    have hrew1 : |(X ω) ^ 4| ^ (2 * j) = (X ω) ^ (2 * (4 * j)) := by
      have hX4_nonneg : 0 ≤ (X ω) ^ 4 := by
        have hsq : 0 ≤ ((X ω) ^ 2) ^ 2 := sq_nonneg _
        have hpow_eq : ((X ω) ^ 2) ^ 2 = (X ω) ^ 4 := by ring
        rw [← hpow_eq]
        exact hsq
      calc
        |(X ω) ^ 4| ^ (2 * j) = ((X ω) ^ 4) ^ (2 * j) := by
          rw [abs_of_nonneg hX4_nonneg]
        _ = (X ω) ^ (4 * (2 * j)) := by rw [← pow_mul]
        _ = (X ω) ^ (2 * (4 * j)) := by ring
    have hrew2 : |-(6 * c₀ * (X ω) ^ 2)| ^ (2 * j) =
        |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) := by
      have hXeven_nonneg : 0 ≤ (X ω) ^ (2 * (2 * j)) := by
        have hsq : 0 ≤ ((X ω) ^ (2 * j)) ^ 2 := sq_nonneg _
        have hpow : 0 ≤ (X ω) ^ ((2 * j) * 2) := by
          simpa [pow_mul] using hsq
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow
      have hXeven : |X ω| ^ (2 * (2 * j)) = (X ω) ^ (2 * (2 * j)) := by
        rw [← abs_pow]
        exact abs_of_nonneg hXeven_nonneg
      rw [abs_neg, abs_mul, mul_pow, abs_pow, ← pow_mul, hXeven]
    have hrew3 : |X ω| ^ (2 * (2 * j)) = (X ω) ^ (2 * (2 * j)) := by
      have hXeven_nonneg : 0 ≤ (X ω) ^ (2 * (2 * j)) := by
        have hsq : 0 ≤ ((X ω) ^ (2 * j)) ^ 2 := sq_nonneg _
        have hpow : 0 ≤ (X ω) ^ ((2 * j) * 2) := by
          simpa [pow_mul] using hsq
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpow
      rw [← abs_pow]
      exact abs_of_nonneg hXeven_nonneg
    calc
      |wickPower 4 mass κ ω y| ^ (2 * j)
        = |(X ω) ^ 4 + -(6 * c₀ * (X ω) ^ 2) + 3 * c₀ ^ 2| ^ (2 * j) := by
            rw [hwick]
      _ ≤ 3 ^ (2 * j - 1) *
            (|(X ω) ^ 4| ^ (2 * j) + |-(6 * c₀ * (X ω) ^ 2)| ^ (2 * j) +
              |3 * c₀ ^ 2| ^ (2 * j)) := hpow
      _ = 3 ^ (2 * j - 1) *
            ((X ω) ^ (2 * (4 * j)) + |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) +
              |3 * c₀ ^ 2| ^ (2 * j)) := by
            rw [hrew1, hrew2]
  have hbound := integral_mono hint hupper hpoint
  calc
    ∫ ω, |wickPower 4 mass κ ω y| ^ (2 * j) ∂μ
      ≤
        ∫ ω,
          3 ^ (2 * j - 1) *
            ((X ω) ^ (2 * (4 * j)) + |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) +
              |3 * c₀ ^ 2| ^ (2 * j)) ∂μ := hbound
    _ =
        3 ^ (2 * j - 1) *
          (∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
            |6 * c₀| ^ (2 * j) * ∫ ω, (X ω) ^ (2 * (2 * j)) ∂μ +
            |3 * c₀ ^ 2| ^ (2 * j)) := by
          have hX4' : Integrable (fun ω => |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j))) μ :=
            hX4.const_mul _
          have hsplit1 :
              ∫ ω,
                  (X ω) ^ (2 * (4 * j)) +
                    (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)) ∂μ
                =
              ∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
                ∫ ω, (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)) ∂μ := by
            simpa using integral_add hX8 (hX4'.add (integrable_const _))
          have hsplit2 :
              ∫ ω, (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)) ∂μ
                =
              ∫ ω, |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) ∂μ +
                ∫ ω, |3 * c₀ ^ 2| ^ (2 * j) ∂μ := by
            simpa using integral_add hX4' (integrable_const _)
          calc
            ∫ ω,
                3 ^ (2 * j - 1) *
                  ((X ω) ^ (2 * (4 * j)) +
                    |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)) ∂μ
              = 3 ^ (2 * j - 1) *
                  ∫ ω,
                    ((X ω) ^ (2 * (4 * j)) +
                      (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j))) ∂μ := by
                      rw [integral_const_mul]
                      congr 1
                      apply integral_congr_ae
                      filter_upwards with ω
                      ring
            _ = 3 ^ (2 * j - 1) *
                  (∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
                    ∫ ω, (|6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) + |3 * c₀ ^ 2| ^ (2 * j)) ∂μ) := by
                      rw [hsplit1]
            _ = 3 ^ (2 * j - 1) *
                  (∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
                    (∫ ω, |6 * c₀| ^ (2 * j) * (X ω) ^ (2 * (2 * j)) ∂μ +
                      ∫ ω, |3 * c₀ ^ 2| ^ (2 * j) ∂μ)) := by
                      rw [hsplit2]
            _ = 3 ^ (2 * j - 1) *
                  (∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
                    (|6 * c₀| ^ (2 * j) * ∫ ω, (X ω) ^ (2 * (2 * j)) ∂μ +
                      |3 * c₀ ^ 2| ^ (2 * j))) := by
                      rw [integral_const_mul, integral_const]
                      simp [Measure.real]
            _ = 3 ^ (2 * j - 1) *
                  (∫ ω, (X ω) ^ (2 * (4 * j)) ∂μ +
                    |6 * c₀| ^ (2 * j) * ∫ ω, (X ω) ^ (2 * (2 * j)) ∂μ +
                    |3 * c₀ ^ 2| ^ (2 * j)) := by ring
    _ ≤
        3 ^ (2 * j - 1) * (M8 + |6 * c₀| ^ (2 * j) * M4 + |3 * c₀ ^ 2| ^ (2 * j)) := by
          gcongr
          · simpa [X, μ, rawFieldEval, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hM8 y hy
          · simpa [X, μ, rawFieldEval, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hM4 y hy

/-- Product-space integrability of even moments of a single quartic Wick field
over a compact spacetime region. -/
private theorem wickPower_even_integrable_prod
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff)
    (j : ℕ) (hj : 0 < j) :
    Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        |wickPower 4 params.mass κ p.1 p.2| ^ (2 * j))
      ((freeFieldMeasure params.mass params.mass_pos).prod
        (MeasureTheory.volume.restrict Λ.toSet)) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D =>
        |wickPower 4 params.mass κ p.1 p.2| ^ (2 * j))
      (μ.prod ν) := by
    have hsm :
        StronglyMeasurable
          (fun p : FieldConfig2D × Spacetime2D =>
            ‖wickPower 4 params.mass κ p.1 p.2‖ ^ (2 * j)) := by
      simpa using (wickPower_stronglyMeasurable_uncurry 4 params.mass κ).norm.pow (2 * j)
    simpa [Real.norm_eq_abs] using hsm.aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · filter_upwards with y
    let q : ℝ≥0∞ := ((2 * j : ℕ) : ℝ≥0∞)
    have hq_ne_top : q ≠ ⊤ := by
      exact ENNReal.coe_ne_top
    have hmem :
        MemLp (fun ω : FieldConfig2D => wickPower 4 params.mass κ ω y) q μ := by
      exact wickPower_memLp 4 params.mass params.mass_pos κ y hq_ne_top
    have hint' :
        Integrable (fun ω : FieldConfig2D => |wickPower 4 params.mass κ ω y| ^ q.toReal) μ := by
      simpa [Real.norm_eq_abs] using hmem.integrable_norm_rpow'
    have hq_toReal : q.toReal = ((2 * j : ℕ) : ℝ) := by
      simp [q]
    convert hint' using 1
    ext ω
    rw [hq_toReal, Real.rpow_natCast]
  · obtain ⟨M, hMnn, hM⟩ := wickPower_even_moment_bounded_on_compact
      params.mass params.mass_pos κ Λ.toSet Λ.toSet_isCompact j hj
    have hsm_prod :
        StronglyMeasurable
          (fun p : FieldConfig2D × Spacetime2D =>
            ‖wickPower 4 params.mass κ p.1 p.2‖ ^ (2 * j)) := by
      simpa using (wickPower_stronglyMeasurable_uncurry 4 params.mass κ).norm.pow (2 * j)
    have hsm0 : AEStronglyMeasurable
        (fun y => ∫ ω, ‖|wickPower 4 params.mass κ ω y| ^ (2 * j)‖ ∂μ) ν := by
      have hsm0' :
          AEStronglyMeasurable
            (fun y => ∫ ω, ‖wickPower 4 params.mass κ ω y‖ ^ (2 * j) ∂μ) ν :=
        (StronglyMeasurable.integral_prod_left hsm_prod).aestronglyMeasurable
      simpa [Real.norm_eq_abs] using hsm0'
    have hν_fin : ν Set.univ < ⊤ := by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact Λ.toSet_isCompact.measure_lt_top
    letI : IsFiniteMeasure ν := ⟨hν_fin⟩
    have hconst : Integrable (fun _ : Spacetime2D => ‖M‖) ν := integrable_const ‖M‖
    apply hconst.mono hsm0
    filter_upwards [MeasureTheory.ae_restrict_mem Λ.toSet_measurableSet] with y hy
    have hI_nonneg :
        0 ≤ ∫ x, ‖|wickPower 4 params.mass κ x y| ^ (2 * j)‖ ∂μ := by
      exact integral_nonneg fun _ => by positivity
    rw [Real.norm_of_nonneg hI_nonneg, Real.norm_of_nonneg hMnn]
    simpa [Real.norm_eq_abs, abs_of_nonneg hMnn] using hM y hy

/-- Finite even moments of cutoff interaction differences. This is now a closed
derived theorem; the remaining Nelson frontier is only the comparison inequality
between these moments and the `L²` shell size. -/
theorem interactionCutoff_sub_even_integrable
    (params : Phi4Params) (Λ : Rectangle) (κ₁ κ₂ : UVCutoff)
    (j : ℕ) (hj : 0 < j) :
    Integrable
      (fun ω : FieldConfig2D =>
        |interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω| ^ (2 * j))
      (freeFieldMeasure params.mass params.mass_pos) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D =>
        |wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j))
      (μ.prod ν) := by
    have hsm :
        StronglyMeasurable
          (fun p : FieldConfig2D × Spacetime2D =>
            ‖wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2‖ ^ (2 * j)) := by
      simpa using
        (((wickPower_stronglyMeasurable_uncurry 4 params.mass κ₂).sub
          (wickPower_stronglyMeasurable_uncurry 4 params.mass κ₁)).norm.pow (2 * j))
    simpa [Real.norm_eq_abs] using hsm.aestronglyMeasurable
  have hκ₂ := wickPower_even_integrable_prod params Λ κ₂ j hj
  have hκ₁ := wickPower_even_integrable_prod params Λ κ₁ j hj
  have hsum : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        |wickPower 4 params.mass κ₂ p.1 p.2| ^ (2 * j) +
          |wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j))
      (μ.prod ν) := hκ₂.add hκ₁
  have hdom : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        2 ^ (2 * j - 1) *
          (|wickPower 4 params.mass κ₂ p.1 p.2| ^ (2 * j) +
            |wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j)))
      (μ.prod ν) := hsum.const_mul _
  have hprod :
      Integrable
        (fun p : FieldConfig2D × Spacetime2D =>
          |wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j))
        (μ.prod ν) := by
    apply hdom.mono hmeas
    filter_upwards with p
    have hm2j : 0 < 2 * j := Nat.mul_pos (by norm_num) hj
    have hsum_nonneg :
        0 ≤
          |wickPower 4 params.mass κ₂ p.1 p.2| ^ (2 * j) +
            |wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j) := by
      positivity
    have hpow :=
      abs_add_pow_le_two_mul_sum_pow
        (wickPower 4 params.mass κ₂ p.1 p.2)
        (-wickPower 4 params.mass κ₁ p.1 p.2)
        hm2j
    have hsum_nonneg' :
        0 ≤
          |wickPower 4 params.mass κ₁ p.1 p.2| ^ (2 * j) +
            |wickPower 4 params.mass κ₂ p.1 p.2| ^ (2 * j) := by
      positivity
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc, abs_of_nonneg hsum_nonneg'] using hpow
  simpa using interactionCutoff_sub_even_integrable_of_prod params Λ κ₁ κ₂ j hj hprod

/-- The L² expectation E[(wickPower 4 mass κ · y)²] is uniformly bounded on compact sets.
    The proof computes the integral explicitly as a polynomial in σ²(y) = Cov(δ_{κ,y}, δ_{κ,y})
    using the Gaussian moment recursion, then uses continuity of σ²(y) (from
    uvMollifier_continuous) to bound the polynomial on the compact set. -/
theorem wickPower_sq_expectation_bounded_on_compact (mass : ℝ) (hmass : 0 < mass)
    (κ : UVCutoff) (K : Set Spacetime2D) (hK : IsCompact K) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ y ∈ K,
      ∫ ω, (wickPower 4 mass κ ω y) ^ 2
        ∂(freeFieldMeasure mass hmass) ≤ M := by
  set T := freeCovarianceCLM mass hmass
  set μ := freeFieldMeasure mass hmass
  set c₀ := regularizedPointCovariance mass κ
  set covFun : Spacetime2D → ℝ := fun y =>
    GaussianField.covariance T (uvMollifier κ y) (uvMollifier κ y)
  -- The polynomial Q(t) = 105t⁴ - 180c₀t³ + 126c₀²t² - 36c₀³t + 9c₀⁴
  -- equals E[(He₄(X;c₀))²] when X ~ N(0,t)
  set Q : ℝ → ℝ := fun t => 105 * t ^ 4 - 180 * c₀ * t ^ 3 + 126 * c₀ ^ 2 * t ^ 2 -
    36 * c₀ ^ 3 * t + 9 * c₀ ^ 4
  -- The integral equals Q(covFun(y)) by explicit Gaussian moment computation
  have hintegral_eq : ∀ y, ∫ ω, (wickPower 4 mass κ ω y) ^ 2 ∂μ = Q (covFun y) := by
    intro y
    set f := uvMollifier κ y
    show ∫ ω, (wickMonomial 4 c₀ (ω f)) ^ 2 ∂μ = Q (covFun y)
    simp only [wickMonomial_four]
    simp_rw [show ∀ ω : FieldConfig2D,
      ((ω f) ^ 4 - 6 * c₀ * (ω f) ^ 2 + 3 * c₀ ^ 2) ^ 2 =
      (ω f) ^ 8 + ((-12) * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      ((-36) * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) from fun ω => by ring]
    have hi8 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 8) μ :=
      power_integrable_ai mass hmass f 8
    have hi6 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 6) μ :=
      power_integrable_ai mass hmass f 6
    have hi4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4) μ :=
      power_integrable_ai mass hmass f 4
    have hi2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2) μ :=
      power_integrable_ai mass hmass f 2
    -- Split integral into sum (use exact/have instead of rw to handle Pi.add matching)
    have s1 : ∫ ω, ((ω f) ^ 8 + (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)))) ∂μ =
      ∫ ω, (ω f) ^ 8 ∂μ + ∫ ω, (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) ∂μ :=
      integral_add hi8 ((hi6.const_mul _).add ((hi4.const_mul _).add
        ((hi2.const_mul _).add (integrable_const _))))
    have s2 : ∫ ω, (-12 * c₀ * (ω f) ^ 6 + (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4))) ∂μ =
      ∫ ω, (-12 * c₀ * (ω f) ^ 6) ∂μ + ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)) ∂μ :=
      integral_add (hi6.const_mul _) ((hi4.const_mul _).add
        ((hi2.const_mul _).add (integrable_const _)))
    have s3 : ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4 +
      (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4)) ∂μ =
      ∫ ω, (42 * c₀ ^ 2 * (ω f) ^ 4) ∂μ +
      ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4) ∂μ :=
      integral_add (hi4.const_mul _) ((hi2.const_mul _).add (integrable_const _))
    have s4 : ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2 + 9 * c₀ ^ 4) ∂μ =
      ∫ ω, (-36 * c₀ ^ 3 * (ω f) ^ 2) ∂μ + ∫ _, 9 * c₀ ^ 4 ∂μ :=
      integral_add (hi2.const_mul _) (integrable_const _)
    rw [s1, s2, s3, s4,
        integral_const_mul, integral_const_mul, integral_const_mul, integral_const]
    -- Gaussian even moments: E[X²]=σ², E[X⁴]=3σ⁴, E[X⁶]=15σ⁶, E[X⁸]=105σ⁸
    have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = covFun y := by
      simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
      exact cross_moment_eq_covariance T f f
    have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * (covFun y) ^ 2 := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
      push_cast; ring
    have h6 : ∫ ω : FieldConfig2D, (ω f) ^ 6 ∂μ = 15 * (covFun y) ^ 3 := by
      rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion_ai mass hmass f 4, h4]
      push_cast; ring
    have h8 : ∫ ω : FieldConfig2D, (ω f) ^ 8 ∂μ = 105 * (covFun y) ^ 4 := by
      rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion_ai mass hmass f 6, h6]
      push_cast; ring
    rw [h8, h6, h4, h2]; simp [Measure.real, measure_univ]; ring
  -- The integral is nonneg (integral of a square)
  have hintegral_nonneg : ∀ y, 0 ≤ ∫ ω, (wickPower 4 mass κ ω y) ^ 2 ∂μ :=
    fun y => integral_nonneg (fun ω => sq_nonneg _)
  -- covFun is continuous (uvMollifier_continuous + T CLM + inner continuous)
  have hcov_cont : Continuous covFun := by
    have h1 := uvMollifier_continuous κ
    have h2 : Continuous (fun y => T (uvMollifier κ y)) := T.continuous.comp h1
    exact continuous_inner.comp (h2.prodMk h2)
  -- Q ∘ covFun is continuous
  have hF_cont : Continuous (fun y => Q (covFun y)) :=
    (by continuity : Continuous Q).comp hcov_cont
  -- On compact K, Q(covFun(y)) is bounded above
  by_cases hKne : K.Nonempty
  · obtain ⟨y₀, hy₀, hmax⟩ := hK.exists_isMaxOn hKne hF_cont.continuousOn
    refine ⟨Q (covFun y₀), ?_, fun y hy => ?_⟩
    · rw [← hintegral_eq]; exact hintegral_nonneg y₀
    · rw [hintegral_eq]; exact hmax hy
  · exact ⟨0, le_rfl, fun y hy => absurd hy
      (Set.not_nonempty_iff_eq_empty.mp hKne ▸ Set.notMem_empty y)⟩

/-- The function (ω, x) ↦ (wickPower 4 mass κ ω x)² is integrable on the product
    of the free field measure with Lebesgue measure restricted to Λ.
    Uses Fubini's criterion (integrable_prod_iff'): integrable in ω for each y,
    and the ω-integral is integrable in y over Λ. -/
theorem wickPower_sq_integrable_prod (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ p.1 p.2) ^ 2)
      ((freeFieldMeasure params.mass params.mass_pos).prod
        (MeasureTheory.volume.restrict Λ.toSet)) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  letI : IsProbabilityMeasure μ := freeFieldMeasure_isProbability params.mass params.mass_pos
  -- Joint AEStronglyMeasurable for wickPower² on the product
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D => (wickPower 4 params.mass κ p.1 p.2) ^ 2)
      (μ.prod ν) := by
    exact ((wickPower_stronglyMeasurable_uncurry 4 params.mass κ).pow 2).aestronglyMeasurable
  rw [MeasureTheory.integrable_prod_iff' hmeas]
  constructor
  · -- (1) For a.e. y ∂ν, ω ↦ wickPower(ω,y)² is integrable ∂μ
    -- This follows from wickPower_sq_integrable for every y
    filter_upwards with y
    exact wickPower_sq_integrable params.mass params.mass_pos κ y
  · -- (2) y ↦ ∫ ‖wickPower(ω,y)²‖ dμ(ω) is integrable ∂ν
    -- Since (wickPower ω y)² ≥ 0, ‖·‖ = id, so this is y ↦ ∫ (wickPower ω y)² dμ
    -- The function is bounded on compact Λ (uniform L² bound) and ν is finite
    obtain ⟨M, hMnn, hM⟩ := wickPower_sq_expectation_bounded_on_compact
      params.mass params.mass_pos κ Λ.toSet Λ.toSet_isCompact
    -- Show the norm simplifies since squares are nonneg
    have hnorm_eq : (fun y => ∫ ω, ‖(wickPower 4 params.mass κ ω y) ^ 2‖ ∂μ) =
        (fun y => ∫ ω, (wickPower 4 params.mass κ ω y) ^ 2 ∂μ) := by
      ext y; congr 1; ext ω; exact Real.norm_of_nonneg (sq_nonneg _)
    rw [hnorm_eq]
    -- Measurability of the partial integral
    have hsm : AEStronglyMeasurable
        (fun y => ∫ ω, (wickPower 4 params.mass κ ω y) ^ 2 ∂μ) ν :=
      (StronglyMeasurable.integral_prod_left
        ((wickPower_stronglyMeasurable_uncurry 4 params.mass κ).pow 2)).aestronglyMeasurable
    -- ν is a finite measure (Λ compact)
    have hν_fin : ν Set.univ < ⊤ := by
      rw [MeasureTheory.Measure.restrict_apply_univ]
      exact Λ.toSet_isCompact.measure_lt_top
    -- Use Integrable.mono with constant function M (integrable on finite measure)
    haveI : IsFiniteMeasure ν := ⟨hν_fin⟩
    have hconst : Integrable (fun _ : Spacetime2D => M) ν := integrable_const M
    apply hconst.mono hsm
    -- a.e. bound: on ν = vol.restrict Λ, a.e. y ∈ Λ.toSet
    filter_upwards [MeasureTheory.ae_restrict_mem Λ.toSet_measurableSet] with y hy
    rw [Real.norm_of_nonneg (integral_nonneg (fun ω => sq_nonneg _)),
        Real.norm_of_nonneg hMnn]
    exact hM y hy

/-- The cutoff interaction is square-integrable under the free field measure.
    This is a consequence of the Gaussian structure: V_{Λ,κ} is an integral
    of polynomials of Gaussian random variables over a bounded region. -/
theorem interactionCutoff_sq_integrable (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  -- interactionCutoff ω = coupling * ∫_Λ wickPower 4 mass κ ω x dx
  -- (interactionCutoff ω)² = coupling² * (∫_Λ w dx)²
  -- By Cauchy-Schwarz: (∫_Λ w dx)² ≤ vol(Λ) * ∫_Λ w² dx
  -- So it suffices to show ω ↦ ∫_Λ w² dx is integrable (Fubini)
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  unfold interactionCutoff
  -- (coupling * ∫_Λ w dx)² = coupling² * (∫_Λ w dx)²
  have h_eq : (fun ω => (params.coupling * ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2) =
      (fun ω => params.coupling ^ 2 * (∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2) := by
    ext ω; ring
  rw [h_eq]
  apply Integrable.const_mul
  -- Need: ω ↦ (∫_Λ w dx)² is integrable ∂μ
  -- By Fubini (wickPower_sq_integrable_prod): (ω,x) ↦ w² is integrable on μ × ν
  -- By integral_prod_left: ω ↦ ∫ w² dν is integrable ∂μ
  -- By Cauchy-Schwarz: (∫_Λ w dx)² ≤ vol(Λ) * ∫_Λ w² dx, so ‖(∫_Λ w)²‖ ≤ ‖vol * ∫ w²‖
  have hprod := wickPower_sq_integrable_prod params Λ κ
  have hfub : Integrable (fun ω => ∫ x, (wickPower 4 params.mass κ ω x) ^ 2 ∂ν) μ :=
    hprod.integral_prod_left
  -- The dominating function is vol(Λ) * ∫ w² dν, which is integrable
  have hdom : Integrable (fun ω => (MeasureTheory.volume Λ.toSet).toReal *
      ∫ x, (wickPower 4 params.mass κ ω x) ^ 2 ∂ν) μ := hfub.const_mul _
  apply hdom.mono
  · -- AEStronglyMeasurable for (∫_Λ w)²
    -- The spatial integral is strongly measurable (same as interactionCutoff proof)
    have hmeas_int : @StronglyMeasurable FieldConfig2D ℝ _ instMeasurableSpaceConfiguration
        (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) := by
      show StronglyMeasurable fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x
      have h_eq : (fun ω => ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) =
          (fun ω => ∫ x, Λ.toSet.indicator (fun x => wickPower 4 params.mass κ ω x) x) := by
        ext ω; rw [integral_indicator Λ.toSet_measurableSet]
      rw [h_eq]
      apply StronglyMeasurable.integral_prod_right
      apply StronglyMeasurable.indicator
      · exact wickPower_stronglyMeasurable_uncurry 4 params.mass κ
      · exact Λ.toSet_measurableSet.preimage measurable_snd
    exact (StronglyMeasurable.pow hmeas_int 2).aestronglyMeasurable
  · -- Pointwise bound: ‖(∫_Λ w)²‖ ≤ ‖vol * ∫ w²‖ a.e.
    filter_upwards with ω
    -- LHS: ‖(∫_Λ w)²‖ = (∫_Λ w)² (since squares are nonneg)
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    -- RHS: ‖vol * ∫ w²‖ = vol * ∫ w² (both nonneg)
    rw [Real.norm_of_nonneg (mul_nonneg ENNReal.toReal_nonneg
      (integral_nonneg (fun x => sq_nonneg _)))]
    -- Now: (∫_Λ w)² ≤ vol * ∫_Λ w² by Cauchy-Schwarz
    -- Convert ∫ ... ∂ν to ∫ ... in Λ.toSet
    change (∫ x in Λ.toSet, wickPower 4 params.mass κ ω x) ^ 2 ≤
      (MeasureTheory.volume Λ.toSet).toReal *
      ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x ^ 2
    -- Apply Cauchy-Schwarz (Jensen)
    apply sq_setIntegral_le_volume_mul_setIntegral_sq
    · exact Λ.toSet_measurableSet
    · -- wickPower is integrable on Λ (continuous on compact, hence integrable)
      exact (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    · -- wickPower² is integrable on Λ
      exact ((wickPower_continuous_in_x 4 params.mass κ ω).pow 2).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    · exact Λ.toSet_volume_ne_top

/-- The cutoff interaction is in L² under the free field measure. -/
theorem interactionCutoff_memLp_two (params : Phi4Params) (Λ : Rectangle)
    (κ : UVCutoff) :
    MemLp (interactionCutoff params Λ κ) 2
      (freeFieldMeasure params.mass params.mass_pos) :=
  (memLp_two_iff_integrable_sq
    (interactionCutoff_aestronglyMeasurable params Λ κ)).2
    (interactionCutoff_sq_integrable params Λ κ)
