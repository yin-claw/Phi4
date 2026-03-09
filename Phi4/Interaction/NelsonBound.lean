/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.UVInfra

/-!
# Nelson Bounds for Interaction Analytic Inputs

This file contains the negative-exponential / lower-tail branch of the
interaction analysis: deterministic Wick lower bounds, reference cutoffs,
hypercontractive Markov reductions, and the remaining Nelson-side frontier
statements.
-/

noncomputable section

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal

/-! ## Nelson's uniform exponential moment bound (Simon Theorem V.14)

The core analytic estimate: for any p > 0, the *negative* exponential moments
E[exp(-p V_{Λ,κ})] are bounded uniformly in the UV cutoff κ.

**Statement-level corrections:**
1. The original statement (`gap_exponential_moment_geometric_bound`) asked for geometric
   decay E[exp(θ|V|)] ≤ D·rⁿ with r < 1. This is mathematically impossible: under a
   probability measure, exp(θ|V|) ≥ 1 always. See `test/proofideas_interaction_next_steps.lean`.
2. The intermediate statement (`gap_exp_interaction_uniform_bound` with |V|) asked for
   E[exp(p|V_κ|)] ≤ C uniformly. This is also false: V_κ is in the 4th Wiener chaos,
   so tails decay like exp(-c√t), making E[exp(p|V_κ|)] = ∞ for any p > 0.

The correct statement uses *negative* exponential moments E[exp(-pV_κ)]. The key insight
is that V_κ = λ∫:φ⁴:dx is NOT symmetric: :φ⁴:_{c_κ} ≥ -6c_κ² pointwise (bounded below),
but unbounded above (heavily right-skewed). So exp(-pV_κ) ≤ exp(6pλc_κ²|Λ|) is finite
for each κ, and Nelson's more sophisticated argument (using hypercontractivity + covariance
splitting) shows the bound is uniform in κ.

Reference: Simon, "The P(φ)₂ Euclidean Field Theory", Theorem V.14;
Glimm-Jaffe, "Quantum Physics", Chapter 8.6. -/

/-- Deterministic lower bound for the cutoff interaction.

    This is the spatially integrated form of the pointwise Wick lower bound
    `:φ⁴:_{c_κ} ≥ -6 c_κ²`. It is uniform in the field configuration `ω`. -/
theorem interactionCutoff_lower_bound
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) (ω : FieldConfig2D) :
    -(params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
      (MeasureTheory.volume Λ.toSet).toReal))
      ≤ interactionCutoff params Λ κ ω := by
  let c : ℝ := regularizedPointCovariance params.mass κ
  have hwick_lower : ∀ x ∈ Λ.toSet, -(6 * c ^ 2 : ℝ) ≤ wickPower 4 params.mass κ ω x := by
    intro x hx
    simp [wickPower, wickMonomial_four, c]
    nlinarith [sq_nonneg (rawFieldEval params.mass κ ω x ^ 2 - 3 * c)]
  have hwick_int :
      IntegrableOn (fun x : Spacetime2D => wickPower 4 params.mass κ ω x) Λ.toSet volume := by
    exact
      (wickPower_continuous_in_x 4 params.mass κ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
  have hset :
      -(6 * c ^ 2 : ℝ) * volume.real Λ.toSet ≤
        ∫ x in Λ.toSet, wickPower 4 params.mass κ ω x := by
    rw [measureReal_def]
    exact
      MeasureTheory.setIntegral_ge_of_const_le_real
        (μ := volume) (s := Λ.toSet)
        (f := fun x : Spacetime2D => wickPower 4 params.mass κ ω x)
        (c := -(6 * c ^ 2 : ℝ))
        Λ.toSet_measurableSet Λ.toSet_volume_ne_top hwick_lower hwick_int
  have hcoupling : 0 ≤ params.coupling := le_of_lt params.coupling_pos
  have hscaled := mul_le_mul_of_nonneg_left hset hcoupling
  rw [measureReal_def] at hscaled
  unfold interactionCutoff
  nlinarith [hscaled]

/-- If the negative threshold is below the deterministic cutoff lower bound,
    the lower-tail event is empty. This is the first cutoffwise reduction used
    in Nelson's argument. -/
theorem interactionCutoff_neg_tail_eq_empty
    (params : Phi4Params) (Λ : Rectangle) (κ : UVCutoff) {t : ℝ}
    (ht :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} = ∅ := by
  ext ω
  constructor
  · intro hω
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false] at hω ⊢
    have hlower := interactionCutoff_lower_bound params Λ κ ω
    linarith
  · intro hω
    simp at hω

/-- If a reference cutoff `κ₀` already satisfies the deterministic lower bound
    `V_{Λ,κ₀} ≥ -t`, then any stronger lower-tail event for another cutoff `κ`
    reduces to a lower-tail event for the difference `V_{Λ,κ} - V_{Λ,κ₀}`. This
    isolates the genuinely fluctuating shell term in Nelson's argument. -/
theorem interactionCutoff_neg_tail_subset_of_sub_tail
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t s : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + s)} ⊆
      {ω : FieldConfig2D |
        interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω < -s} := by
  intro ω hω
  simp only [Set.mem_setOf_eq] at hω ⊢
  have hlower := interactionCutoff_lower_bound params Λ κ₀ ω
  linarith

/-- Measure version of `interactionCutoff_neg_tail_subset_of_sub_tail`. -/
theorem measure_interactionCutoff_neg_tail_le_sub_tail
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t s : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + s)}
      ≤
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D |
        interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω < -s} := by
  exact measure_mono (interactionCutoff_neg_tail_subset_of_sub_tail params Λ κ κ₀ hκ₀)

/-- Markov's inequality at even moment order: for a measurable real-valued
function `Y` and `j ≥ 1`, `P(|Y| > 1)` is bounded by the `2j`-th moment. -/
theorem markov_even_moment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} (j : ℕ)
    (hint : Integrable (fun ω => |Y ω| ^ (2 * j)) μ) :
    μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := by
  have hsub : {ω | 1 < |Y ω|} ⊆ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact one_le_pow₀ (le_of_lt hω)
  calc
    μ {ω | 1 < |Y ω|}
      ≤ μ {ω | (1 : ℝ) ≤ |Y ω| ^ (2 * j)} := measure_mono hsub
    _ ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) :=
        hint.measure_le_integral
          (ae_of_all _ (fun ω => pow_nonneg (abs_nonneg _) _))
          (fun ω hω => hω)

/-- `4 - log 16` is positive, since `16 < exp 4`. This is the decay exponent
appearing in the Markov optimization step. -/
private theorem four_sub_log_sixteen_pos : 0 < 4 - Real.log 16 := by
  have : Real.log 16 < 4 := by
    rw [show (4 : ℝ) = Real.log (Real.exp 4) from (Real.log_exp 4).symm]
    exact Real.log_lt_log (by positivity) (by
      calc (16 : ℝ) = 2 ^ 4 := by norm_num
        _ < Real.exp 1 ^ 4 :=
          pow_lt_pow_left₀ Real.exp_one_gt_two (by norm_num) (by norm_num)
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num)
  linarith

/-- Markov optimization: when the even moments satisfy the hypercontractive-type
growth `((C j)^4 * ε^2)^j`, one can choose an optimal integer moment order
producing a double-exponential decay scale `exp(-c / sqrt ε)`. -/
theorem markov_optimization_exists_j
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ (c : ℝ) (j : ℕ), 0 < c ∧ 0 < j ∧
      (C * ↑j) ^ (4 * j) * ε ^ (2 * j) ≤ Real.exp (-(c / Real.sqrt ε)) := by
  set e₁ := Real.exp 1
  set β := 4 - Real.log 16
  set j_real := 1 / (e₁ * C * Real.sqrt ε)
  set j := Nat.ceil j_real
  set c := β / (e₁ * C)
  refine ⟨c, j, ?_, ?_, ?_⟩
  · exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
  ·
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos (mul_pos (Real.exp_pos 1) hC) (Real.sqrt_pos.mpr hε))
    exact Nat.ceil_pos.mpr hj_real_pos
  ·
    have he₁_pos : 0 < e₁ := Real.exp_pos 1
    have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have heC_pos : 0 < e₁ * C := mul_pos he₁_pos hC
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos heC_pos hsqrt_pos)
    have hj_real_ge_one : 1 ≤ j_real := by
      rw [one_le_div (mul_pos heC_pos hsqrt_pos)]
      have hsq_le : Real.sqrt ε ≤ 1 / (e₁ * C) := by
        rw [Real.sqrt_le_left]
        · rwa [div_pow, one_pow]
        · exact div_nonneg (by norm_num) (le_of_lt heC_pos)
      calc e₁ * C * Real.sqrt ε
          ≤ e₁ * C * (1 / (e₁ * C)) :=
            mul_le_mul_of_nonneg_left hsq_le (le_of_lt heC_pos)
        _ = 1 := by field_simp
    have hj_le : (j : ℝ) ≤ 2 * j_real := by
      have : (j : ℝ) ≤ j_real + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (le_of_lt hj_real_pos))
      linarith
    have hj_ge : j_real ≤ (j : ℝ) := Nat.le_ceil j_real
    have hCj_le : C * (j : ℝ) ≤ 2 / (e₁ * Real.sqrt ε) := by
      calc C * (j : ℝ) ≤ C * (2 * j_real) :=
              mul_le_mul_of_nonneg_left hj_le (le_of_lt hC)
        _ = 2 * (C / (e₁ * C * Real.sqrt ε)) := by ring
        _ = 2 / (e₁ * Real.sqrt ε) := by
            congr 1
            field_simp
    have hbase_le : (C * (j : ℝ)) ^ 4 * ε ^ 2 ≤ 16 / e₁ ^ 4 := by
      have h1 : (C * (j : ℝ)) ^ 4 ≤ (2 / (e₁ * Real.sqrt ε)) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hCj_le 4
      have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
      have h2 : (2 / (e₁ * Real.sqrt ε)) ^ 4 * ε ^ 2 = 16 / e₁ ^ 4 := by
        have he₁_ne : e₁ ≠ 0 := ne_of_gt he₁_pos
        have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
        field_simp
        rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, hsq]
        ring
      linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ε)]
    have hrewrite : (C * (j : ℝ)) ^ (4 * j) * ε ^ (2 * j) =
        ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ (j : ℕ) := by
      rw [mul_pow, pow_mul, pow_mul, pow_mul]
      ring
    rw [hrewrite]
    have hbase_nonneg : 0 ≤ (C * (j : ℝ)) ^ 4 * ε ^ 2 := by positivity
    have hpow_le : ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ j ≤ (16 / e₁ ^ 4) ^ j :=
      pow_le_pow_left₀ hbase_nonneg hbase_le j
    have hlog_ratio : Real.log (16 / e₁ ^ 4) = Real.log 16 - 4 := by
      rw [Real.log_div (by positivity : (16 : ℝ) ≠ 0) (by positivity : e₁ ^ 4 ≠ 0)]
      congr 1
      rw [Real.log_pow, Real.log_exp]
      norm_num
    have hratio_pos : 0 < 16 / e₁ ^ 4 := by positivity
    have hratio_eq : 16 / e₁ ^ 4 = Real.exp (-β) := by
      rw [← Real.exp_log hratio_pos, hlog_ratio]
      congr 1
      ring
    have hpow_eq : (16 / e₁ ^ 4) ^ j = Real.exp (-(β * (j : ℝ))) := by
      rw [hratio_eq, ← Real.exp_nat_mul, mul_comm]
      congr 1
      ring
    have hβj_ge : β * j_real ≤ β * (j : ℝ) :=
      mul_le_mul_of_nonneg_left hj_ge (le_of_lt four_sub_log_sixteen_pos)
    have hβj_real_eq : β * j_real = c / Real.sqrt ε := by
      simp only [c, j_real]
      field_simp
    have hexp_le : Real.exp (-(β * (j : ℝ))) ≤ Real.exp (-(c / Real.sqrt ε)) := by
      apply Real.exp_le_exp_of_le
      linarith
    linarith [hpow_le, hpow_eq, hexp_le]

/-- Explicit decay constant appearing in the optimized Markov bound. -/
private def markovTailConstant (C : ℝ) : ℝ :=
  (4 - Real.log 16) / (Real.exp 1 * C)

/-- Explicit version of the Markov optimization step. The decay constant depends
only on `C`, not on the scale `ε`. -/
private theorem markov_optimization_explicit_bound
    (C : ℝ) (hC : 0 < C) (ε : ℝ) (hε : 0 < ε)
    (hε_small : ε ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ j : ℕ, 0 < j ∧
      (C * ↑j) ^ (4 * j) * ε ^ (2 * j) ≤
        Real.exp (-(markovTailConstant C / Real.sqrt ε)) := by
  set e₁ := Real.exp 1
  set β := 4 - Real.log 16
  set j_real := 1 / (e₁ * C * Real.sqrt ε)
  set j := Nat.ceil j_real
  have hj : 0 < j := by
    have hj_real_pos : 0 < j_real :=
      div_pos one_pos (mul_pos (mul_pos (Real.exp_pos 1) hC) (Real.sqrt_pos.mpr hε))
    exact Nat.ceil_pos.mpr hj_real_pos
  refine ⟨j, hj, ?_⟩
  have he₁_pos : 0 < e₁ := Real.exp_pos 1
  have hsqrt_pos : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
  have heC_pos : 0 < e₁ * C := mul_pos he₁_pos hC
  have hj_real_pos : 0 < j_real := div_pos one_pos (mul_pos heC_pos hsqrt_pos)
  have hj_real_ge_one : 1 ≤ j_real := by
    rw [one_le_div (mul_pos heC_pos hsqrt_pos)]
    have hsq_le : Real.sqrt ε ≤ 1 / (e₁ * C) := by
      rw [Real.sqrt_le_left]
      · rwa [div_pow, one_pow]
      · exact div_nonneg (by norm_num) (le_of_lt heC_pos)
    calc e₁ * C * Real.sqrt ε
        ≤ e₁ * C * (1 / (e₁ * C)) :=
          mul_le_mul_of_nonneg_left hsq_le (le_of_lt heC_pos)
      _ = 1 := by field_simp
  have hj_le : (j : ℝ) ≤ 2 * j_real := by
    have : (j : ℝ) ≤ j_real + 1 :=
      le_of_lt (Nat.ceil_lt_add_one (le_of_lt hj_real_pos))
    linarith
  have hj_ge : j_real ≤ (j : ℝ) := Nat.le_ceil j_real
  have hCj_le : C * (j : ℝ) ≤ 2 / (e₁ * Real.sqrt ε) := by
    calc C * (j : ℝ) ≤ C * (2 * j_real) :=
            mul_le_mul_of_nonneg_left hj_le (le_of_lt hC)
      _ = 2 * (C / (e₁ * C * Real.sqrt ε)) := by ring
      _ = 2 / (e₁ * Real.sqrt ε) := by
          congr 1
          field_simp
  have hbase_le : (C * (j : ℝ)) ^ 4 * ε ^ 2 ≤ 16 / e₁ ^ 4 := by
    have h1 : (C * (j : ℝ)) ^ 4 ≤ (2 / (e₁ * Real.sqrt ε)) ^ 4 :=
      pow_le_pow_left₀ (by positivity) hCj_le 4
    have hsq : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt (le_of_lt hε)
    have h2 : (2 / (e₁ * Real.sqrt ε)) ^ 4 * ε ^ 2 = 16 / e₁ ^ 4 := by
      have he₁_ne : e₁ ≠ 0 := ne_of_gt he₁_pos
      have hsqrt_ne : Real.sqrt ε ≠ 0 := ne_of_gt hsqrt_pos
      field_simp
      rw [show (Real.sqrt ε) ^ 4 = ((Real.sqrt ε) ^ 2) ^ 2 from by ring, hsq]
      ring
    linarith [mul_le_mul_of_nonneg_right h1 (sq_nonneg ε)]
  have hrewrite :
      (C * (j : ℝ)) ^ (4 * j) * ε ^ (2 * j) =
        ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ (j : ℕ) := by
    rw [mul_pow, pow_mul, pow_mul, pow_mul]
    ring
  rw [hrewrite]
  have hbase_nonneg : 0 ≤ (C * (j : ℝ)) ^ 4 * ε ^ 2 := by positivity
  have hpow_le : ((C * (j : ℝ)) ^ 4 * ε ^ 2) ^ j ≤ (16 / e₁ ^ 4) ^ j :=
    pow_le_pow_left₀ hbase_nonneg hbase_le j
  have hlog_ratio : Real.log (16 / e₁ ^ 4) = Real.log 16 - 4 := by
    rw [Real.log_div (by positivity : (16 : ℝ) ≠ 0) (by positivity : e₁ ^ 4 ≠ 0)]
    congr 1
    rw [Real.log_pow, Real.log_exp]
    norm_num
  have hratio_pos : 0 < 16 / e₁ ^ 4 := by positivity
  have hratio_eq : 16 / e₁ ^ 4 = Real.exp (-β) := by
    rw [← Real.exp_log hratio_pos, hlog_ratio]
    congr 1
    ring
  have hpow_eq : (16 / e₁ ^ 4) ^ j = Real.exp (-(β * (j : ℝ))) := by
    rw [hratio_eq, ← Real.exp_nat_mul, mul_comm]
    congr 1
    ring
  have hβj_ge : β * j_real ≤ β * (j : ℝ) :=
    mul_le_mul_of_nonneg_left hj_ge (le_of_lt four_sub_log_sixteen_pos)
  have hconst_eq :
      markovTailConstant C / Real.sqrt ε = β * j_real := by
    simp only [markovTailConstant, β, j_real, e₁]
    field_simp
  have hexp_le :
      Real.exp (-(β * (j : ℝ))) ≤
        Real.exp (-(markovTailConstant C / Real.sqrt ε)) := by
    apply Real.exp_le_exp_of_le
    rw [hconst_eq]
    linarith
  linarith [hpow_le, hpow_eq, hexp_le]

/-- Explicit constant form of `markov_hypercontractive_tail`. This is the
uniform decay constant needed to build `t`-uniform Nelson bounds later. -/
theorem markov_hypercontractive_tail_explicit
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {C σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable (fun ω => |Y ω| ^ (2 * j)) μ ∧
      ∫ ω, |Y ω| ^ (2 * j) ∂μ ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    μ {ω | 1 < |Y ω|} ≤
      ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
  obtain ⟨j, hj, hopt⟩ := markov_optimization_explicit_bound C hC σ hσ hσ_small
  obtain ⟨hint, hmom⟩ := hmoment j hj
  calc
    μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) :=
      markov_even_moment j hint
    _ ≤ ENNReal.ofReal ((C * ↑j) ^ (4 * j) * σ ^ (2 * j)) :=
      ENNReal.ofReal_le_ofReal hmom
    _ ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) :=
      ENNReal.ofReal_le_ofReal hopt

/-- Markov's inequality with optimized moment order turns hypercontractive even
moment growth into a double-exponential tail bound. -/
theorem markov_hypercontractive_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {Y : Ω → ℝ} {C σ : ℝ} (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable (fun ω => |Y ω| ^ (2 * j)) μ ∧
      ∫ ω, |Y ω| ^ (2 * j) ∂μ ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ c : ℝ, 0 < c ∧
      μ {ω | 1 < |Y ω|} ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := by
  obtain ⟨c, j, hc, hj, hopt⟩ := markov_optimization_exists_j C hC σ hσ hσ_small
  obtain ⟨hint, hmom⟩ := hmoment j hj
  refine ⟨c, hc, ?_⟩
  calc
    μ {ω | 1 < |Y ω|}
      ≤ ENNReal.ofReal (∫ ω, |Y ω| ^ (2 * j) ∂μ) := markov_even_moment j hint
    _ ≤ ENNReal.ofReal ((C * ↑j) ^ (4 * j) * σ ^ (2 * j)) :=
        ENNReal.ofReal_le_ofReal hmom
    _ ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) :=
        ENNReal.ofReal_le_ofReal hopt

/-- Assumption-explicit Nelson reduction step.

    If a reference cutoff `κ₀` has already been chosen so that the deterministic
    lower bound gives `V_{Λ,κ₀} ≥ -t`, and if the cutoff difference
    `V_{Λ,κ} - V_{Λ,κ₀}` satisfies the hypercontractive even-moment bounds from
    `markov_hypercontractive_tail`, then the stronger lower-tail event
    `V_{Λ,κ} < -(t + 1)` already has double-exponential decay. The remaining
    work for Nelson's argument is therefore to construct `κ₀(t)` and prove the
    even-moment bound for the shell difference. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t C σ : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t)
    (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ c : ℝ, 0 < c ∧
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)} ≤
      ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let Y : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  obtain ⟨c, hc, htailY⟩ :=
    markov_hypercontractive_tail (μ := μ) (Y := Y) (C := C) (σ := σ)
      hC hσ
      (by
        intro j hj
        simpa [μ, Y] using hmoment j hj)
      hσ_small
  refine ⟨c, hc, ?_⟩
  have hsub_abs : {ω : FieldConfig2D | Y ω < -(1 : ℝ)} ⊆ {ω : FieldConfig2D | 1 < |Y ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hyneg : Y ω < 0 := by linarith
    rw [abs_of_neg hyneg]
    linarith
  calc
    μ {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)}
      ≤ μ {ω : FieldConfig2D | Y ω < -(1 : ℝ)} := by
          simpa [μ, Y] using
            measure_interactionCutoff_neg_tail_le_sub_tail params Λ κ κ₀
              (t := t) (s := (1 : ℝ)) hκ₀
    _ ≤ μ {ω : FieldConfig2D | 1 < |Y ω|} := measure_mono hsub_abs
    _ ≤ ENNReal.ofReal (Real.exp (-(c / Real.sqrt σ))) := htailY

/-- Explicit-constant Nelson reduction step. This is the same reduction as
`interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments`,
but with the optimized Markov constant exposed directly. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments_explicit
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff) {t C σ : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t)
    (hC : 0 < C) (hσ : 0 < σ)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j))
    (hσ_small : σ ≤ 1 / (Real.exp 1 * C) ^ 2) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)} ≤
    ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let Y : FieldConfig2D → ℝ :=
    fun ω => interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω
  have htailY :
      μ {ω | 1 < |Y ω|} ≤
        ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
    exact markov_hypercontractive_tail_explicit (μ := μ) (Y := Y) hC hσ
      (by
        intro j hj
        simpa [μ, Y] using hmoment j hj)
      hσ_small
  have hsub_abs : {ω : FieldConfig2D | Y ω < -(1 : ℝ)} ⊆ {ω : FieldConfig2D | 1 < |Y ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω ⊢
    have hyneg : Y ω < 0 := by linarith
    rw [abs_of_neg hyneg]
    linarith
  calc
    μ {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 1)}
      ≤ μ {ω : FieldConfig2D | Y ω < -(1 : ℝ)} := by
          simpa [μ, Y] using
            measure_interactionCutoff_neg_tail_le_sub_tail params Λ κ κ₀
              (t := t) (s := (1 : ℝ)) hκ₀
    _ ≤ μ {ω : FieldConfig2D | 1 < |Y ω|} := measure_mono hsub_abs
    _ ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := htailY

/-- Canonical Nelson reference-scale prefactor.

    The denominator is inflated by `((volume Λ.toSet).toReal + 1)` to avoid a
    separate positivity theorem for the rectangle volume in the cutoff-choice
    construction. This still gives the required deterministic lower bound
    `V_{Λ,κ₀(t)} ≥ -(t + 1)`. -/
private def nelsonReferenceAlpha (params : Phi4Params) (Λ : Rectangle) (K : ℝ) : ℝ :=
  1 / (K * Real.sqrt (6 * params.coupling * ((MeasureTheory.volume Λ.toSet).toReal + 1)))

/-- Logarithmic shift used to absorb the additive constant in the covariance-growth
bound `c_κ ≤ C₀ + K log κ`. -/
private def nelsonReferenceLogShift (K C₀ : ℝ) : ℝ :=
  C₀ / K

/-- Canonical reference cutoff `κ₀(t)` for Nelson's argument. -/
private def nelsonReferenceCutoff
    (params : Phi4Params) (Λ : Rectangle) (K C₀ t : ℝ) : UVCutoff :=
  ⟨Real.exp
      (nelsonReferenceAlpha params Λ K * Real.sqrt (t + 1) - nelsonReferenceLogShift K C₀),
    Real.exp_pos _⟩

/-- If the regularized point covariance grows at most logarithmically in the
    cutoff, then the canonical Nelson reference cutoff `κ₀(t)` forces the
    deterministic lower bound to sit below `t + 1`.

    This isolates the cutoff-choice part of Nelson's argument from the genuine
    moment estimate on `V_{Λ,κ} - V_{Λ,κ₀(t)}`. -/
theorem interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound
    (params : Phi4Params) (Λ : Rectangle) {K : ℝ} (hK : 0 < K)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    {t : ℝ} (ht : 0 ≤ t) :
    params.coupling *
      (6 * (regularizedPointCovariance params.mass
          (nelsonReferenceCutoff params Λ K C₀ t)) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1 := by
  let V : ℝ := (MeasureTheory.volume Λ.toSet).toReal
  let D : ℝ := 6 * params.coupling * (V + 1)
  let α : ℝ := nelsonReferenceAlpha params Λ K
  let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ t
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    have hV1 : 0 < V + 1 := by linarith
    exact mul_pos (mul_pos (by positivity) params.coupling_pos) hV1
  have hκ₀_log :
      Real.log κ₀.κ = α * Real.sqrt (t + 1) - C₀ / K := by
    dsimp [κ₀, nelsonReferenceCutoff]
    simp [α, nelsonReferenceLogShift]
  have hα_pos : 0 < α := by
    dsimp [α, nelsonReferenceAlpha]
    exact one_div_pos.mpr (mul_pos hK (Real.sqrt_pos.mpr hD_pos))
  have ht1_nonneg : 0 ≤ t + 1 := by linarith
  have hmain_nonneg : 0 ≤ K * (α * Real.sqrt (t + 1)) := by
    exact mul_nonneg hK.le (mul_nonneg hα_pos.le (Real.sqrt_nonneg _))
  have hcov_nonneg : 0 ≤ regularizedPointCovariance params.mass κ₀ := by
    rw [regularizedPointCovariance_eq_covariance params.mass params.mass_pos κ₀]
    exact covariance_self_nonneg params.mass params.mass_pos (uvMollifier κ₀ 0)
  have hcov_upper :
      regularizedPointCovariance params.mass κ₀ ≤ K * (α * Real.sqrt (t + 1)) := by
    have hcov0 := hcov κ₀
    have hK_ne : K ≠ 0 := ne_of_gt hK
    rw [hκ₀_log] at hcov0
    have hcancel :
        C₀ + K * (α * Real.sqrt (t + 1) - C₀ / K) = K * (α * Real.sqrt (t + 1)) := by
      field_simp [hK_ne]
      ring
    rw [hcancel] at hcov0
    exact hcov0
  have hcov_sq :
      (regularizedPointCovariance params.mass κ₀) ^ 2 ≤
        (K * (α * Real.sqrt (t + 1))) ^ 2 := by
    nlinarith [hcov_upper, hcov_nonneg, hmain_nonneg]
  have hmul :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 * V) ≤
        params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) := by
    have hconst_nonneg : 0 ≤ params.coupling * (6 * V) := by
      have h6V : 0 ≤ 6 * V := by nlinarith [hV_nonneg]
      exact mul_nonneg (le_of_lt params.coupling_pos) h6V
    have hscaled := mul_le_mul_of_nonneg_left hcov_sq hconst_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hsqrt_t_sq : Real.sqrt (t + 1) ^ 2 = t + 1 := by
    rw [Real.sq_sqrt ht1_nonneg]
  have htarget :
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) =
        (V / (V + 1)) * (t + 1) := by
    have hsqrt_ne : Real.sqrt D ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr hD_pos)
    have hV1_ne : V + 1 ≠ 0 := by linarith [hD_pos]
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hsqrt_inv_sq : (Real.sqrt D)⁻¹ ^ 2 = 1 / D := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (le_of_lt hD_pos)]
    have hcancel :
        (K * ((1 / (K * Real.sqrt D)) * Real.sqrt (t + 1))) ^ 2 =
          (Real.sqrt D)⁻¹ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt hK, hsqrt_ne]
      rw [Real.sq_sqrt ht1_nonneg]
    calc
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V)
          = params.coupling * (6 * ((Real.sqrt D)⁻¹ ^ 2 * (t + 1)) * V) := by
              dsimp [α, nelsonReferenceAlpha]
              rw [hcancel]
      _ = params.coupling * (6 * ((1 / D) * (t + 1)) * V) := by
            rw [hsqrt_inv_sq]
      _ = ((params.coupling * 6 * V) / D) * (t + 1) := by
            field_simp [hD_ne]
      _ = (V / (V + 1)) * (t + 1) := by
            dsimp [D]
            field_simp [hV1_ne, ne_of_gt params.coupling_pos]
  rw [htarget] at hmul
  have hfrac_le : V / (V + 1) ≤ 1 := by
    have hV1 : 0 < V + 1 := by linarith
    rw [div_le_iff₀ hV1]
    linarith
  nlinarith [hmul, hfrac_le]

/-- Small-cutoff variant of
`interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound`.

If `κ` lies below the canonical reference cutoff `κ₀(t)`, the same logarithmic
covariance-growth input already forces the deterministic lower bound
`V_{Λ,κ} ≥ -(t + 1)`. Only the large-cutoff regime `κ₀(t) ≤ κ` needs the
decaying shell estimate later in Nelson's argument. -/
private theorem interactionCutoff_below_reference_cutoff_le_one_add_of_log_covariance_bound
    (params : Phi4Params) (Λ : Rectangle) {K : ℝ} (hK : 0 < K)
    {C₀ : ℝ} (_hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    (κ : UVCutoff) {t : ℝ} (ht : 0 ≤ t)
    (hκ_le : κ.κ ≤ (nelsonReferenceCutoff params Λ K C₀ t).κ) :
    params.coupling *
      (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1 := by
  let V : ℝ := (MeasureTheory.volume Λ.toSet).toReal
  let D : ℝ := 6 * params.coupling * (V + 1)
  let α : ℝ := nelsonReferenceAlpha params Λ K
  let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ t
  have hV_nonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hD_pos : 0 < D := by
    dsimp [D]
    have hV1 : 0 < V + 1 := by linarith
    exact mul_pos (mul_pos (by positivity) params.coupling_pos) hV1
  have hκ₀_log :
      Real.log κ₀.κ = α * Real.sqrt (t + 1) - C₀ / K := by
    dsimp [κ₀, nelsonReferenceCutoff]
    simp [α, nelsonReferenceLogShift]
  have hα_pos : 0 < α := by
    dsimp [α, nelsonReferenceAlpha]
    exact one_div_pos.mpr (mul_pos hK (Real.sqrt_pos.mpr hD_pos))
  have ht1_nonneg : 0 ≤ t + 1 := by linarith
  have hmain_nonneg : 0 ≤ K * (α * Real.sqrt (t + 1)) := by
    exact mul_nonneg hK.le (mul_nonneg hα_pos.le (Real.sqrt_nonneg _))
  have hcov_nonneg : 0 ≤ regularizedPointCovariance params.mass κ := by
    rw [regularizedPointCovariance_eq_covariance params.mass params.mass_pos κ]
    exact covariance_self_nonneg params.mass params.mass_pos (uvMollifier κ 0)
  have hlog_le : Real.log κ.κ ≤ Real.log κ₀.κ := by
    exact Real.log_le_log (by linarith [κ.hκ]) hκ_le
  have hcov_le_ref :
      regularizedPointCovariance params.mass κ ≤ K * (α * Real.sqrt (t + 1)) := by
    have hlog_scaled :
        C₀ + K * Real.log κ.κ ≤ C₀ + K * Real.log κ₀.κ := by
      nlinarith [mul_le_mul_of_nonneg_left hlog_le hK.le]
    have hcov0 : regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ₀.κ :=
      le_trans (hcov κ) hlog_scaled
    have hK_ne : K ≠ 0 := ne_of_gt hK
    rw [hκ₀_log] at hcov0
    have hcancel :
        C₀ + K * (α * Real.sqrt (t + 1) - C₀ / K) = K * (α * Real.sqrt (t + 1)) := by
      field_simp [hK_ne]
      ring
    rw [hcancel] at hcov0
    exact hcov0
  have hcov_sq :
      (regularizedPointCovariance params.mass κ) ^ 2 ≤
        (K * (α * Real.sqrt (t + 1))) ^ 2 := by
    nlinarith [hcov_le_ref, hcov_nonneg, hmain_nonneg]
  have hmul :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ) ^ 2 * V) ≤
        params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) := by
    have hconst_nonneg : 0 ≤ params.coupling * (6 * V) := by
      have h6V : 0 ≤ 6 * V := by nlinarith [hV_nonneg]
      exact mul_nonneg (le_of_lt params.coupling_pos) h6V
    have hscaled := mul_le_mul_of_nonneg_left hcov_sq hconst_nonneg
    simpa [mul_assoc, mul_left_comm, mul_comm] using hscaled
  have hsqrt_t_sq : Real.sqrt (t + 1) ^ 2 = t + 1 := by
    rw [Real.sq_sqrt ht1_nonneg]
  have htarget :
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V) =
        (V / (V + 1)) * (t + 1) := by
    have hsqrt_ne : Real.sqrt D ≠ 0 := by
      exact ne_of_gt (Real.sqrt_pos.mpr hD_pos)
    have hV1_ne : V + 1 ≠ 0 := by linarith [hD_pos]
    have hD_ne : D ≠ 0 := ne_of_gt hD_pos
    have hsqrt_inv_sq : (Real.sqrt D)⁻¹ ^ 2 = 1 / D := by
      field_simp [hsqrt_ne]
      rw [Real.sq_sqrt (le_of_lt hD_pos)]
    have hcancel :
        (K * ((1 / (K * Real.sqrt D)) * Real.sqrt (t + 1))) ^ 2 =
          (Real.sqrt D)⁻¹ ^ 2 * (t + 1) := by
      field_simp [ne_of_gt hK, hsqrt_ne]
      rw [Real.sq_sqrt ht1_nonneg]
    calc
      params.coupling * (6 * ((K * (α * Real.sqrt (t + 1))) ^ 2) * V)
          = params.coupling * (6 * ((Real.sqrt D)⁻¹ ^ 2 * (t + 1)) * V) := by
              dsimp [α, nelsonReferenceAlpha]
              rw [hcancel]
      _ = params.coupling * (6 * ((1 / D) * (t + 1)) * V) := by
            rw [hsqrt_inv_sq]
      _ = ((params.coupling * 6 * V) / D) * (t + 1) := by
            field_simp [hD_ne]
      _ = (V / (V + 1)) * (t + 1) := by
            dsimp [D]
            field_simp [hV1_ne, ne_of_gt params.coupling_pos]
  rw [htarget] at hmul
  have hfrac_le : V / (V + 1) ≤ 1 := by
    have hV1 : 0 < V + 1 := by linarith
    rw [div_le_iff₀ hV1]
    linarith
  nlinarith [hmul, hfrac_le]

/-- Square-root factorization for the exponentially small Nelson shell scale. -/
private theorem sqrt_exponential_shell_scale
    {σ₀ β t : ℝ} (hσ₀ : 0 < σ₀) :
    Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) =
      Real.sqrt σ₀ * Real.exp (-β * Real.sqrt (t + 2)) := by
  have hexp_sq :
      Real.exp (-2 * β * Real.sqrt (t + 2)) =
        (Real.exp (-β * Real.sqrt (t + 2))) ^ 2 := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc
    Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)))
        = Real.sqrt σ₀ * Real.sqrt (Real.exp (-2 * β * Real.sqrt (t + 2))) := by
            rw [Real.sqrt_mul (le_of_lt hσ₀)]
    _ = Real.sqrt σ₀ * Real.exp (-β * Real.sqrt (t + 2)) := by
          congr 1
          rw [hexp_sq, Real.sqrt_sq_eq_abs]
          exact abs_of_pos (Real.exp_pos _)

/-- Pure-analysis bridge from the Nelson shell scale
`σ₀ * exp(-2β√(t+2))` to a double-exponential exponent in `√(t+1)`. -/
private theorem exp_neg_inv_sqrt_exponential_shell_scale_le
    {M σ₀ β t : ℝ} (hM : 0 ≤ M) (hσ₀ : 0 < σ₀) (hβ : 0 < β) :
    Real.exp (-(M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))))) ≤
      Real.exp (-(M / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1)))) := by
  have hsqrt_eq := sqrt_exponential_shell_scale (σ₀ := σ₀) (β := β) (t := t) hσ₀
  have hsqrtσ₀_ne : Real.sqrt σ₀ ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hσ₀)
  have hexp_ne : Real.exp (-(β * Real.sqrt (t + 2))) ≠ 0 := by positivity
  have hexp_mul :
      Real.exp (-(β * Real.sqrt (t + 2))) * Real.exp (β * Real.sqrt (t + 2)) = 1 := by
    rw [← Real.exp_add]
    rw [show -(β * Real.sqrt (t + 2)) + β * Real.sqrt (t + 2) = 0 by ring, Real.exp_zero]
  have hscale_eq :
      M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) =
        (M / Real.sqrt σ₀) * Real.exp (β * Real.sqrt (t + 2)) := by
    rw [hsqrt_eq]
    field_simp [hsqrtσ₀_ne, hexp_ne]
    have hmul_eq :
        M * (Real.exp (-(β * Real.sqrt (t + 2))) * Real.exp (β * Real.sqrt (t + 2))) =
          M * 1 := by
      exact congrArg (fun z : ℝ => M * z) hexp_mul
    simpa [mul_assoc] using hmul_eq.symm
  have hsqrt_mono : Real.sqrt (t + 1) ≤ Real.sqrt (t + 2) := by
    apply Real.sqrt_le_sqrt
    linarith
  have hexp_mono :
      Real.exp (β * Real.sqrt (t + 1)) ≤ Real.exp (β * Real.sqrt (t + 2)) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hsqrt_mono hβ.le
  have hM_nonneg' : 0 ≤ M / Real.sqrt σ₀ := by
    exact div_nonneg hM (Real.sqrt_nonneg _)
  have hscale_ge :
      M / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1)) ≤
        M / Real.sqrt (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) := by
    rw [hscale_eq]
    exact mul_le_mul_of_nonneg_left hexp_mono hM_nonneg'
  apply Real.exp_le_exp.mpr
  linarith

/-- Stable combined Nelson reduction with an externally supplied reference cutoff
and an explicit exponentially small shell scale.

This theorem avoids the brittle canonical-cutoff bookkeeping and packages the
usable consequence of the current Nelson infrastructure: if the shell-difference
moments are controlled at scale `σ₀ * exp(-2β√(t+2))`, then the lower tail at
level `-(t+2)` already has double-exponential decay in `√(t+1)`. -/
theorem interactionCutoff_neg_tail_of_reference_cutoff_and_exponential_shell_scale
    (params : Phi4Params) (Λ : Rectangle) (κ κ₀ : UVCutoff)
    {t C σ₀ β : ℝ}
    (hκ₀ :
      params.coupling * (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
        (MeasureTheory.volume Λ.toSet).toReal) ≤ t + 1)
    (hC : 0 < C) (hσ₀ : 0 < σ₀) (hβ : 0 < β)
    (hmoment : ∀ j : ℕ, 0 < j →
      Integrable
        (fun ω : FieldConfig2D =>
          |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
        (freeFieldMeasure params.mass params.mass_pos) ∧
      ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
          ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j))
    (hσ_small :
      σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) :
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)} ≤
    ENNReal.ofReal
      (Real.exp (-(markovTailConstant C / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1))))) := by
  let σ : ℝ := σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))
  have hσ_pos : 0 < σ := by
    dsimp [σ]
    exact mul_pos hσ₀ (Real.exp_pos _)
  have htail :
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)} ≤
      ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
    have htail' :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -((t + 1) + 1)} ≤
        ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := by
      have hmoment' : ∀ j : ℕ, 0 < j →
          Integrable
            (fun ω : FieldConfig2D =>
              |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
            (freeFieldMeasure params.mass params.mass_pos) ∧
          ∫ ω, |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ (C * ↑j) ^ (4 * j) * σ ^ (2 * j) := by
        simpa [σ] using hmoment
      have hσ_small' : σ ≤ 1 / (Real.exp 1 * C) ^ 2 := by
        simpa [σ] using hσ_small
      exact
        interactionCutoff_neg_tail_of_reference_cutoff_and_hypercontractive_moments_explicit
          params Λ κ κ₀ (t := t + 1) (C := C) (σ := σ)
          hκ₀ hC hσ_pos hmoment' hσ_small'
    have hshift : -((t + 1) + 1 : ℝ) = -(t + 2) := by ring
    simpa [hshift] using htail'
  have hM_nonneg : 0 ≤ markovTailConstant C := by
    have hM_pos : 0 < markovTailConstant C := by
      dsimp [markovTailConstant]
      exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
    exact hM_pos.le
  calc
    (freeFieldMeasure params.mass params.mass_pos)
      {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(t + 2)}
      ≤ ENNReal.ofReal (Real.exp (-(markovTailConstant C / Real.sqrt σ))) := htail
    _ ≤ ENNReal.ofReal
          (Real.exp (-(markovTailConstant C / Real.sqrt σ₀ * Real.exp (β * Real.sqrt (t + 1))))) := by
        apply ENNReal.ofReal_le_ofReal
        exact exp_neg_inv_sqrt_exponential_shell_scale_le
          (M := markovTailConstant C) hM_nonneg hσ₀ hβ

/-- Canonical Nelson reduction: logarithmic covariance growth plus an explicit
reference-shell moment bound already imply a double-exponential lower-tail
estimate for all cutoffs.

This theorem isolates the remaining Nelson-side mathematics to a single honest
input: a moment bound for the shell difference against the canonical reference
cutoff `κ₀(t)`. Once that input is proved, the cutoffwise lower tail is
finished without further bookkeeping. -/
theorem interactionCutoff_double_exponential_tail_of_log_covariance_and_reference_shell_scale
    (params : Phi4Params) (Λ : Rectangle)
    {K C₀ C σ₀ β : ℝ}
    (hK : 0 < K) (hC₀ : 0 ≤ C₀)
    (hcov :
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ)
    (hC : 0 < C) (hσ₀ : 0 < σ₀) (hβ : 0 < β)
    (hmoment :
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∀ j : ℕ, 0 < j →
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω,
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j))
    (hσ_small :
      ∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) :
    ∃ A B Ctail : ℝ, 0 < A ∧ 0 < B ∧ 0 < Ctail ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤
        ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
  let B : ℝ := markovTailConstant C / Real.sqrt σ₀
  let Ctail : ℝ := β / 2
  let A : ℝ := Real.exp (B * Real.exp (Ctail * Real.sqrt 2))
  have hB_pos : 0 < B := by
    dsimp [B, markovTailConstant]
    refine div_pos ?_ (Real.sqrt_pos.mpr hσ₀)
    exact div_pos four_sub_log_sixteen_pos (mul_pos (Real.exp_pos 1) hC)
  have hCtail_pos : 0 < Ctail := by
    dsimp [Ctail]
    linarith
  have hA_pos : 0 < A := by
    dsimp [A]
    exact Real.exp_pos _
  refine ⟨A, B, Ctail, hA_pos, hB_pos, hCtail_pos, ?_⟩
  intro κ t ht
  by_cases ht_small : t ≤ 2
  · have hμ_le_one :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤ 1 := by
      calc
        (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
          ≤ (freeFieldMeasure params.mass params.mass_pos) Set.univ := by
              apply measure_mono
              intro ω hω
              simp
        _ = 1 := by simp
    have hsqrt_le : Real.sqrt t ≤ Real.sqrt 2 := by
      apply Real.sqrt_le_sqrt
      linarith
    have hexp_le :
        Real.exp (Ctail * Real.sqrt t) ≤ Real.exp (Ctail * Real.sqrt 2) := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_left hsqrt_le hCtail_pos.le
    have hneg_exp_le :
        Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) ≤
          Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      apply Real.exp_le_exp.mpr
      have hB_nonneg : 0 ≤ B := hB_pos.le
      nlinarith [hexp_le, hB_nonneg]
    have hone_le :
        1 ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      have hA_nonneg : 0 ≤ A := by
        exact (Real.exp_pos _).le
      have hone_eq : A * Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) = 1 := by
        dsimp [A]
        rw [← Real.exp_add]
        have : B * Real.exp (Ctail * Real.sqrt 2) + -B * Real.exp (Ctail * Real.sqrt 2) = 0 := by ring
        rw [this, Real.exp_zero]
      calc
        1 = A * Real.exp (-B * Real.exp (Ctail * Real.sqrt 2)) := by
              rw [hone_eq]
        _ ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
              exact mul_le_mul_of_nonneg_left hneg_exp_le hA_nonneg
    calc
      (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
        ≤ 1 := hμ_le_one
      _ = ENNReal.ofReal (1 : ℝ) := by norm_num
      _ ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
            exact ENNReal.ofReal_le_ofReal hone_le
  · have ht_gt : 2 < t := lt_of_not_ge ht_small
    let s : ℝ := t - 2
    have hs_nonneg : 0 ≤ s := by
      dsimp [s]
      linarith
    let κ₀ : UVCutoff := nelsonReferenceCutoff params Λ K C₀ s
    have htail_core :
        (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} ≤
        ENNReal.ofReal
          (Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))) := by
      by_cases hκ_ge : κ₀.κ ≤ κ.κ
      · have hκ₀ :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ₀) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 1 := by
          exact interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound
            params Λ hK hC₀ hcov hs_nonneg
        have hmoment' : ∀ j : ℕ, 0 < j →
            Integrable
              (fun ω : FieldConfig2D =>
                |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j))
              (freeFieldMeasure params.mass params.mass_pos) ∧
            ∫ ω,
                |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
                ∂(freeFieldMeasure params.mass params.mass_pos)
              ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (s + 2))) ^ (2 * j) := by
          intro j hj
          simpa [κ₀, s] using hmoment κ s hs_nonneg hκ_ge j hj
        have hσ_small' :
            σ₀ * Real.exp (-2 * β * Real.sqrt (s + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2 := by
          simpa [s] using hσ_small s hs_nonneg
        simpa [B, κ₀] using
          interactionCutoff_neg_tail_of_reference_cutoff_and_exponential_shell_scale
            params Λ κ κ₀ (t := s) (C := C) (σ₀ := σ₀) (β := β)
            hκ₀ hC hσ₀ hβ hmoment' hσ_small'
      · have hκ_small :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 1 := by
          exact interactionCutoff_below_reference_cutoff_le_one_add_of_log_covariance_bound
            params Λ hK hC₀ hcov κ hs_nonneg (le_of_not_ge hκ_ge)
        have hκ_small' :
            params.coupling *
                (6 * (regularizedPointCovariance params.mass κ) ^ 2 *
                  (MeasureTheory.volume Λ.toSet).toReal)
              ≤ s + 2 := by
          linarith
        have hempty :
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} = ∅ :=
          interactionCutoff_neg_tail_eq_empty params Λ κ (t := s + 2) hκ_small'
        rw [hempty]
        simp
    have hs_plus : s + 2 = t := by
      dsimp [s]
      ring
    have hsqrt_half :
        (1 / 2 : ℝ) * Real.sqrt t ≤ Real.sqrt (t - 1) := by
      have ht1_nonneg : 0 ≤ t - 1 := by linarith
      have hleft_nonneg : 0 ≤ (1 / 2 : ℝ) * Real.sqrt t := by positivity
      have hright_nonneg : 0 ≤ Real.sqrt (t - 1) := Real.sqrt_nonneg _
      have hsq :
          (((1 / 2 : ℝ) * Real.sqrt t) ^ 2) ≤ (Real.sqrt (t - 1)) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt ht, Real.sq_sqrt ht1_nonneg]
        norm_num
        linarith
      nlinarith
    have hsqrt_cmp : Ctail * Real.sqrt t ≤ β * Real.sqrt (s + 1) := by
      have hmul_half : β * ((1 / 2 : ℝ) * Real.sqrt t) ≤ β * Real.sqrt (t - 1) := by
        exact mul_le_mul_of_nonneg_left hsqrt_half hβ.le
      have hs_eq : s + 1 = t - 1 := by
        dsimp [s]
        ring
      calc
        Ctail * Real.sqrt t = β * ((1 / 2 : ℝ) * Real.sqrt t) := by
          dsimp [Ctail]
          ring
        _ ≤ β * Real.sqrt (t - 1) := hmul_half
        _ = β * Real.sqrt (s + 1) := by rw [hs_eq]
    have hexp_cmp :
        Real.exp (Ctail * Real.sqrt t) ≤ Real.exp (β * Real.sqrt (s + 1)) := by
      exact Real.exp_le_exp.mpr hsqrt_cmp
    have htail_cmp :
        Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1)))) ≤
          A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
      have hbase :
          Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1)))) ≤
            Real.exp (-(B * Real.exp (Ctail * Real.sqrt t))) := by
        apply Real.exp_le_exp.mpr
        nlinarith [hexp_cmp, hB_pos.le]
      calc
        Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))
          ≤ Real.exp (-(B * Real.exp (Ctail * Real.sqrt t))) := hbase
        _ ≤ A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by
            have hA_ge_one : 1 ≤ A := by
              dsimp [A]
              have hA_nonneg : 0 ≤ B * Real.exp (Ctail * Real.sqrt 2) := by
                positivity
              simpa using Real.one_le_exp_iff.mpr hA_nonneg
            have hnonneg : 0 ≤ Real.exp (-B * Real.exp (Ctail * Real.sqrt t)) := by positivity
            simpa [one_mul] using mul_le_mul_of_nonneg_right hA_ge_one hnonneg
    calc
      (freeFieldMeasure params.mass params.mass_pos)
          {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t}
        = (freeFieldMeasure params.mass params.mass_pos)
            {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -(s + 2)} := by
              congr 1
              ext ω
              simp only [Set.mem_setOf_eq]
              rw [hs_plus]
      _ ≤ ENNReal.ofReal (Real.exp (-(B * Real.exp (β * Real.sqrt (s + 1))))) := htail_core
      _ ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (Ctail * Real.sqrt t))) := by
            exact ENNReal.ofReal_le_ofReal htail_cmp

/-- Frontier theorem for the logarithmic growth of the regularized point
covariance.

This is the covariance-growth input needed to choose the canonical Nelson
reference cutoff `κ₀(t)`. It is separate from the shell-moment analysis: once
an additive-constant logarithmic bound `C₀ + K log κ` is available, the
deterministic part of the reference-cutoff argument is already closed by
`interactionCutoff_reference_cutoff_le_one_add_of_log_covariance_bound`. -/
theorem gap_regularizedPointCovariance_log_growth
    (params : Phi4Params) :
    ∃ K C₀ : ℝ, 0 < K ∧ 0 ≤ C₀ ∧
      ∀ κ : UVCutoff,
        regularizedPointCovariance params.mass κ ≤ C₀ + K * Real.log κ.κ := by
  sorry

/-- Frontier theorem for the canonical reference-shell even-moment bound in
Nelson's argument.

With a logarithmic covariance-growth constant `K` fixed, the remaining missing
Nelson-side mathematics splits naturally into:
1. a uniform Gaussian-polynomial even-moment comparison for cutoff differences,
2. an explicit `L²` decay bound for the canonical reference shell.

The next two frontier theorems expose exactly those two inputs.

Important theorem-surface note:
- the moment-comparison input must control the **integrated variable**
  `interactionCutoff κ - interactionCutoff κ₀` directly in terms of its own
  `L²` norm;
- a product-space comparison for the pointwise Wick-power difference is too weak
  for downstream use, because Jensen only gives
  `E[(ΔV)^2] ≤ const * ∫∫ d^2`, i.e. in the wrong direction for recovering an
  `L²`-based hypercontractive bound on `ΔV`.

So the genuine missing mathematics here is a fourth-chaos / Nelson
hypercontractive estimate for the integrated cutoff difference itself, not just
a pointwise spacetime moment estimate. -/
theorem gap_interactionCutoff_sub_even_moment_comparison
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (κ κ₀ : UVCutoff) (j : ℕ), 0 < j →
        ∫ ω,
            |interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) *
              (∫ ω,
                  (interactionCutoff params Λ κ ω - interactionCutoff params Λ κ₀ ω) ^ 2
                  ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j := by
  sorry

/-- Frontier theorem for the `L²` size of the canonical reference shell in
Nelson's argument.

This is the genuine covariance-shell decay input on the Nelson side, but only
in the large-cutoff regime `κ₀(t) ≤ κ`. For cutoffs below the reference scale,
the lower tail is handled deterministically by the Wick lower bound, so no
decaying shell estimate should be claimed there. The smallness condition
relative to `C` is bundled here because it is needed by the optimized Markov
step later. -/
theorem gap_interactionCutoff_reference_shell_L2_bound
    (params : Phi4Params) (Λ : Rectangle) (K C₀ C : ℝ) :
    ∃ σ₀ β : ℝ,
      0 < σ₀ ∧ 0 < β ∧
      (∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∫ ω,
            (interactionCutoff params Λ κ ω -
              interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2 := by
  sorry

/-- Derived canonical reference-shell even-moment theorem.

This theorem is no longer a primitive analytic frontier: it is assembled from
the two genuine missing inputs above, namely uniform even-moment comparison and
the explicit large-cutoff `L²` shell decay bound. -/
theorem gap_interactionCutoff_reference_shell_even_moment_bound
    (params : Phi4Params) (Λ : Rectangle) (K C₀ : ℝ) :
    ∃ C σ₀ β : ℝ,
      0 < C ∧ 0 < σ₀ ∧ 0 < β ∧
      (∀ t : ℝ, 0 ≤ t →
        σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2)) ≤ 1 / (Real.exp 1 * C) ^ 2) ∧
      ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
        (nelsonReferenceCutoff params Λ K C₀ t).κ ≤ κ.κ →
        ∀ j : ℕ, 0 < j →
        Integrable
          (fun ω : FieldConfig2D =>
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω,
            |interactionCutoff params Λ κ ω -
                interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω| ^ (2 * j)
            ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤ (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
  obtain ⟨C, hC, hmomentCmp⟩ := gap_interactionCutoff_sub_even_moment_comparison params Λ
  obtain ⟨σ₀, β, hσ₀, hβ, hσ_small, hL2⟩ :=
    gap_interactionCutoff_reference_shell_L2_bound params Λ K C₀ C
  refine ⟨C, σ₀, β, hC, hσ₀, hβ, hσ_small, ?_⟩
  intro κ t ht hκ_ge j hj
  have hint :=
    interactionCutoff_sub_even_integrable params Λ (nelsonReferenceCutoff params Λ K C₀ t) κ j hj
  have hcmp := hmomentCmp κ (nelsonReferenceCutoff params Λ K C₀ t) j hj
  refine ⟨hint, le_trans hcmp ?_⟩
  have hL2' := hL2 κ t ht hκ_ge
  have hpow_le :
      (∫ ω,
          (interactionCutoff params Λ κ ω -
            interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j
        ≤ ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j := by
    exact pow_le_pow_left₀ (by positivity) hL2' j
  calc
    (C * ↑j) ^ (4 * j) *
        (∫ ω,
            (interactionCutoff params Λ κ ω -
              interactionCutoff params Λ (nelsonReferenceCutoff params Λ K C₀ t) ω) ^ 2
            ∂(freeFieldMeasure params.mass params.mass_pos)) ^ j
      ≤ (C * ↑j) ^ (4 * j) * ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j := by
          exact mul_le_mul_of_nonneg_left hpow_le (by positivity)
    _ = (C * ↑j) ^ (4 * j) * (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
          have hpow_eq :
              ((σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ 2) ^ j =
                (σ₀ * Real.exp (-2 * β * Real.sqrt (t + 2))) ^ (2 * j) := by
            rw [← pow_mul]
          rw [hpow_eq]

/-- **Sub-gap A: Double-exponential tail bound for the cutoff interaction.**

    For all t ≥ 0 and all UV cutoffs κ:
      P(V_{Λ,κ} < -t) ≤ A · exp(-B · exp(C · √t))
    where A, B, C > 0 depend on λ, |Λ|, m but NOT on κ.

    This is the core of Nelson's argument (Simon Theorem V.14). The proof uses:
    1. Covariance splitting: split φ_κ = φ_{κ₀} + ψ with κ₀ chosen from an
       additive-constant logarithmic covariance bound
    2. Wick lower bound: V_{κ₀} ≥ -6λc_{κ₀}²|Λ| ≥ -t (by choice of κ₀)
    3. Hence P(V_κ < -t-1) ≤ P(V_κ - V_{κ₀} < -1)
    4. Moment bound: E[(V_κ - V_{κ₀})^{2j}] ≤ (4j²)^{2j} ‖V_κ - V_{κ₀}‖₂^{2j}
       (Gaussian polynomial moment equivalence for 4th-chaos elements)
    5. L² bound: ‖V_κ - V_{κ₀}‖₂ ≤ ε(κ₀) with ε(κ₀) ~ κ₀^{-δ}
    6. Optimize j to get double-exponential tail decay. -/
theorem gap_interaction_double_exponential_tail_bound
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ A B C : ℝ, 0 < A ∧ 0 < B ∧ 0 < C ∧ ∀ (κ : UVCutoff) (t : ℝ), 0 ≤ t →
      (freeFieldMeasure params.mass params.mass_pos)
        {ω : FieldConfig2D | interactionCutoff params Λ κ ω < -t} ≤
      ENNReal.ofReal (A * Real.exp (-B * Real.exp (C * Real.sqrt t))) := by
  obtain ⟨K, C₀, hK, hC₀, hcov⟩ := gap_regularizedPointCovariance_log_growth params
  obtain ⟨Cmom, σ₀, β, hCmom, hσ₀, hβ, hσ_small, hmoment⟩ :=
    gap_interactionCutoff_reference_shell_even_moment_bound params Λ K C₀
  exact
    interactionCutoff_double_exponential_tail_of_log_covariance_and_reference_shell_scale
      params Λ hK hC₀ hcov hCmom hσ₀ hβ hmoment hσ_small

/-- The improper integral ∫₀^∞ exp(pt - B·exp(C·√t)) dt is finite for all p, B, C > 0.
    Proof: for t ≥ T₀, B·exp(C·√t) ≥ (p+1)t, so the integrand ≤ exp(-t). -/
theorem integral_exp_linear_minus_double_exp_finite
    {p B C : ℝ} (hB : 0 < B) (hC : 0 < C) :
    IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi 0) volume := by
  set T₀ := max 1 (24 * (p + 1) / (B * C ^ 4)) with hT₀_def
  have hT₀_pos : 0 < T₀ := lt_of_lt_of_le one_pos (le_max_left _ _)
  have hBC4_pos : 0 < B * C ^ 4 := mul_pos hB (pow_pos hC 4)
  have hexp_quartic : ∀ t : ℝ, 0 ≤ t →
      C ^ 4 * t ^ 2 / 24 ≤ Real.exp (C * Real.sqrt t) := by
    intro t ht
    have hsqrt_nn : 0 ≤ C * Real.sqrt t := mul_nonneg (le_of_lt hC) (Real.sqrt_nonneg t)
    have h1 := Real.pow_div_factorial_le_exp (C * Real.sqrt t) hsqrt_nn 4
    have h2 : (C * Real.sqrt t) ^ 4 = C ^ 4 * t ^ 2 := by
      rw [mul_pow]; congr 1; rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt ht]
    rw [h2] at h1; norm_num [Nat.factorial] at h1; linarith
  have h_dom : ∀ t ≥ T₀, p * t - B * Real.exp (C * Real.sqrt t) ≤ -t := by
    intro t ht
    have ht_pos : 0 ≤ t := le_of_lt (lt_of_lt_of_le hT₀_pos ht)
    have ht_T₀ : t ≥ 24 * (p + 1) / (B * C ^ 4) := le_trans (le_max_right _ _) ht
    have h_coeff : (p + 1) * 24 ≤ B * C ^ 4 * t := by
      have := div_le_iff₀ hBC4_pos |>.mp ht_T₀; linarith
    have h_exp := hexp_quartic t ht_pos
    have h_B_exp : B * (C ^ 4 * t ^ 2 / 24) ≤ B * Real.exp (C * Real.sqrt t) :=
      mul_le_mul_of_nonneg_left h_exp (le_of_lt hB)
    nlinarith
  have hf_cont : Continuous (fun t : ℝ => Real.exp (p * t - B * Real.exp (C * Real.sqrt t))) :=
    by fun_prop
  have h_Ioi : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioi T₀) volume := by
    apply Integrable.mono (exp_neg_integrableOn_Ioi T₀ one_pos)
      (hf_cont.aestronglyMeasurable.restrict)
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_exp.2 (by linarith [h_dom t (Set.mem_Ioi.mp ht).le])
  have h_Ioc : IntegrableOn (fun t => Real.exp (p * t - B * Real.exp (C * Real.sqrt t)))
      (Set.Ioc 0 T₀) volume :=
    (hf_cont.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  rw [show Set.Ioi (0 : ℝ) = Set.Ioc 0 T₀ ∪ Set.Ioi T₀ from
    (Set.Ioc_union_Ioi_eq_Ioi (le_of_lt hT₀_pos)).symm]
  exact h_Ioc.union h_Ioi

/-- FTC: ∫₀^y p·exp(pt) dt = exp(py) - 1. -/
private theorem interval_integral_p_mul_exp (p y : ℝ) :
    ∫ t in (0 : ℝ)..y, p * Real.exp (p * t) = Real.exp (p * y) - 1 := by
  have hderiv : ∀ x ∈ Set.uIcc 0 y,
      HasDerivAt (fun t => Real.exp (p * t)) (p * Real.exp (p * x)) x := by
    intro x _
    exact ((by simpa using (hasDerivAt_id x).const_mul p :
      HasDerivAt (fun t => p * t) p x).exp.congr_deriv (by ring))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    ((continuous_const.mul (Real.continuous_exp.comp
      (continuous_const.mul continuous_id'))).intervalIntegrable _ _)]
  simp [mul_zero]

/-- Pure-analysis lemma: if a random variable has double-exponential lower tail,
    then all negative exponential moments are finite.

    From the layer-cake identity:
      E[exp(-pX)] ≤ 1 + ∫₀^∞ p·exp(pt) · P(X < -t) dt
    and the double-exponential tail bound P(X < -t) ≤ A·exp(-B·exp(C·√t)):
      ∫₀^∞ p·exp(pt)·A·exp(-B·exp(C·√t)) dt < ∞
    because exp(C·√t) dominates pt for large t. -/
theorem neg_exp_moment_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
    ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤
      1 + p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) := by
  -- Abbreviations
  set g : ℝ → ℝ := fun t => p * Real.exp (p * t) with hg_def
  set f_tail : ℝ → ℝ := fun t =>
    p * A * Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) with hf_def
  -- FTC: ∫₀^{max(-x,0)} g = exp(p·max(-x,0)) - 1
  have hftc : ∀ ω : Ω, ∫ t in (0 : ℝ)..max (-X ω) 0, g t =
      Real.exp (p * max (-X ω) 0) - 1 :=
    fun ω => interval_integral_p_mul_exp p _
  have hI_nn : ∀ ω : Ω, 0 ≤ ∫ t in (0 : ℝ)..max (-X ω) 0, g t := fun ω => by
    rw [hftc]; linarith [Real.one_le_exp (mul_nonneg hp.le (le_max_right (-X ω) 0))]
  -- Layer-cake formula
  have hlc : ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ =
      ∫⁻ t in Set.Ioi (0 : ℝ), μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) :=
    lintegral_comp_eq_lintegral_meas_lt_mul μ
      (by filter_upwards with ω; exact le_max_right _ _)
      ((hX.neg.max measurable_const).aemeasurable)
      (fun t _ => (continuous_const.mul (Real.continuous_exp.comp
        (continuous_const.mul continuous_id'))).intervalIntegrable _ _)
      (by filter_upwards with t; exact mul_nonneg hp.le (Real.exp_pos _).le)
  -- {max(-X,0) > t} = {X < -t} for t > 0
  have hset_eq : ∀ t : ℝ, 0 < t →
      μ {a : Ω | t < max (-X a) 0} = μ {a | X a < -t} := by
    intro t ht; congr 1; ext ω; simp only [Set.mem_setOf_eq]
    constructor
    · intro h; by_contra h_neg; push_neg at h_neg
      exact not_lt.mpr (max_le (by linarith) ht.le) h
    · intro h; exact lt_max_of_lt_left (by linarith)
  -- Tail integrand is IntegrableOn (Ioi 0)
  have hf_intOn : IntegrableOn f_tail (Set.Ioi 0) volume := by
    have := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
    exact this.const_mul (p * A)
  -- *** Main lintegral bound ***
  -- ∫⁻ ofReal(exp(-pX)) ≤ 1 + ∫⁻_{t>0} ofReal(f_tail t)
  have h_lint_bound : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≤
      1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ
        ≤ ∫⁻ ω, (1 + ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t)) ∂μ := by
          apply lintegral_mono; intro ω; simp only
          rw [show (1 : ENNReal) = ENNReal.ofReal 1 from ENNReal.ofReal_one.symm,
              ← ENNReal.ofReal_add one_pos.le (hI_nn ω), hftc]
          apply ENNReal.ofReal_le_ofReal
          linarith [Real.exp_le_exp.2 (show -(p * X ω) ≤ p * max (-X ω) 0
            by nlinarith [le_max_left (-X ω) 0])]
      _ = 1 + ∫⁻ ω, ENNReal.ofReal (∫ t in (0 : ℝ)..max (-X ω) 0, g t) ∂μ := by
          rw [lintegral_add_left measurable_const]; simp [lintegral_const, measure_univ]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | t < max (-X a) 0} * ENNReal.ofReal (g t) := by rw [hlc]
      _ = 1 + ∫⁻ t in Set.Ioi (0 : ℝ),
            μ {a | X a < -t} * ENNReal.ofReal (g t) := by
          congr 1; apply setLIntegral_congr_fun measurableSet_Ioi
          intro t ht; simp only [Set.mem_Ioi] at ht
          show μ {a | t < max (-X a) 0} * _ = μ {a | X a < -t} * _
          rw [hset_eq t ht]
      _ ≤ 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) := by
          apply add_le_add_right _ 1
          apply setLIntegral_mono (Measurable.ennreal_ofReal (by fun_prop))
          intro t ht
          have ht' := Set.mem_Ioi.mp ht
          calc μ {a | X a < -t} * ENNReal.ofReal (g t)
              ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))) *
                ENNReal.ofReal (g t) :=
                mul_le_mul_left (htail t ht'.le) _
            _ = ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t)) * g t) :=
                (ENNReal.ofReal_mul (mul_nonneg hA.le (Real.exp_pos _).le)).symm
            _ = ENNReal.ofReal (f_tail t) := by
                congr 1; simp only [hg_def, hf_def]
                rw [show p * t - B * Real.exp (C_tail * Real.sqrt t) =
                  -B * Real.exp (C_tail * Real.sqrt t) + p * t from by ring, Real.exp_add]
                ring
  -- *** Convert to real integral ***
  -- The lintegral of ofReal(f_tail) equals ofReal(∫ f_tail) since f_tail ≥ 0 and integrable
  have h_lint_eq : ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) =
      ENNReal.ofReal (∫ t in Set.Ioi 0, f_tail t) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf_intOn
      (by filter_upwards with t; exact mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le)]
  -- The lintegral is finite
  have h_lint_ne_top : ∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ ≠ ⊤ := by
    have h_rhs_ne_top : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
      rw [h_lint_eq]
      exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
    exact ne_top_of_le_ne_top h_rhs_ne_top h_lint_bound
  -- Integrability
  have h_integrable : Integrable (fun ω => Real.exp (-(p * X ω))) μ := by
    refine ⟨((hX.const_mul p).neg.exp).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_norm]
    calc ∫⁻ a, ENNReal.ofReal ‖Real.exp (-(p * X a))‖ ∂μ
        = ∫⁻ a, ENNReal.ofReal (Real.exp (-(p * X a))) ∂μ := by
          congr 1; ext ω; rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      _ < ⊤ := h_lint_ne_top.lt_top
  refine ⟨h_integrable, ?_⟩
  -- Real integral bound
  have h_real : (∫ ω, Real.exp (-(p * X ω)) ∂μ : ℝ) =
      (∫⁻ ω, ENNReal.ofReal (Real.exp (-(p * X ω))) ∂μ).toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae
      (by filter_upwards with ω; exact (Real.exp_pos _).le)
      ((hX.const_mul p).neg.exp).aestronglyMeasurable]
  rw [h_real]
  have h_rhs_ne : 1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t) ≠ ⊤ := by
    rw [h_lint_eq]
    exact ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, ENNReal.ofReal_ne_top⟩
  have h_rhs_val : (1 + ∫⁻ t in Set.Ioi (0 : ℝ), ENNReal.ofReal (f_tail t)).toReal =
      1 + ∫ t in Set.Ioi 0, f_tail t := by
    rw [h_lint_eq, ENNReal.toReal_add ENNReal.one_ne_top ENNReal.ofReal_ne_top,
        ENNReal.toReal_one, ENNReal.toReal_ofReal (setIntegral_nonneg measurableSet_Ioi
          (fun t _ => mul_nonneg (mul_nonneg hp.le hA.le) (Real.exp_pos _).le))]
  rw [show 1 + p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) =
    1 + ∫ t in Set.Ioi 0, f_tail t from by
      simp only [hf_def]; rw [← integral_const_mul]]
  rw [← h_rhs_val]
  exact (ENNReal.toReal_le_toReal h_lint_ne_top h_rhs_ne).mpr h_lint_bound

/-- Bounded form of `neg_exp_moment_of_double_exponential_tail`: under a double-exponential
    lower tail bound, the negative exponential moment E[exp(-pX)] is bounded by some
    finite constant K. This decouples downstream uses from the specific layer-cake bound. -/
theorem neg_exp_moment_bounded_of_double_exponential_tail
    {Ω : Type*} [MeasurableSpace Ω] {μ : MeasureTheory.Measure Ω}
    [MeasureTheory.IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X)
    {A B C_tail : ℝ} (hA : 0 < A) (hB : 0 < B) (hC : 0 < C_tail)
    (htail : ∀ t : ℝ, 0 ≤ t →
      μ {ω | X ω < -t} ≤ ENNReal.ofReal (A * Real.exp (-B * Real.exp (C_tail * Real.sqrt t))))
    (p : ℝ) (hp : 0 < p) :
    ∃ K : ℝ, 0 < K ∧
      Integrable (fun ω => Real.exp (-(p * X ω))) μ ∧
      ∫ ω, Real.exp (-(p * X ω)) ∂μ ≤ K := by
  obtain ⟨hint, hbound⟩ := neg_exp_moment_of_double_exponential_tail hX hA hB hC htail p hp
  refine ⟨1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)), ?_, hint, hbound⟩
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
      Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
    mul_nonneg (mul_nonneg hp.le hA.le)
      (setIntegral_nonneg measurableSet_Ioi (fun t _ => (Real.exp_pos _).le))
  linarith

theorem gap_exp_neg_interaction_uniform_bound (params : Phi4Params) (Λ : Rectangle) :
    ∀ p : ℝ, 0 < p →
      ∃ C : ℝ, 0 < C ∧ ∀ κ : UVCutoff,
        Integrable
          (fun ω : FieldConfig2D =>
            Real.exp (-(p * interactionCutoff params Λ κ ω)))
          (freeFieldMeasure params.mass params.mass_pos) ∧
        ∫ ω : FieldConfig2D,
          Real.exp (-(p * interactionCutoff params Λ κ ω))
          ∂(freeFieldMeasure params.mass params.mass_pos) ≤ C := by
  intro p hp
  -- Obtain double-exponential tail bound (uniform in κ)
  obtain ⟨A, B, C_tail, hA, hB, hC, htail⟩ :=
    gap_interaction_double_exponential_tail_bound params Λ
  -- The layer-cake integral is finite
  have hI := @integral_exp_linear_minus_double_exp_finite p B C_tail hB hC
  -- Set uniform bound
  set K := 1 + p * A * ∫ t in Set.Ioi 0,
    Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t))
  refine ⟨K, ?_, fun κ => ?_⟩
  · -- K > 0: K = 1 + (nonneg) ≥ 1 > 0
    have : 0 ≤ p * A * ∫ t in Set.Ioi 0,
        Real.exp (p * t - B * Real.exp (C_tail * Real.sqrt t)) :=
      mul_nonneg (mul_nonneg (le_of_lt hp) (le_of_lt hA))
        (setIntegral_nonneg measurableSet_Ioi (fun t _ => le_of_lt (Real.exp_pos _)))
    linarith
  · -- Apply neg_exp_moment to each cutoff
    have hX_meas : Measurable (interactionCutoff params Λ κ) :=
      (interactionCutoff_stronglyMeasurable params Λ κ).measurable
    exact neg_exp_moment_of_double_exponential_tail hX_meas hA hB hC
      (fun t ht => htail κ t ht) p hp
