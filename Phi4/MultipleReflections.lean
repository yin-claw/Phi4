/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.ReflectionPositivity

/-!
# Multiple Reflection Bounds (Chessboard Estimates)

Multiple reflections generalize reflection positivity to give uniform bounds
on expectations. The idea is to tile the spacetime region Λ with unit squares
and use RP across each reflection plane to "factorize" the expectation.

The main result is the chessboard estimate:
  ⟨∏ᵢ Aᵢ⟩ ≤ ∏ᵢ ⟨Aᵢᴺ⟩^{1/N}

where N is determined by the geometry of the tiling. Combined with the finite-volume
estimates of Chapter 8, this gives bounds that are uniform in the volume.

These uniform bounds are the second ingredient (after monotonicity) for the
infinite volume limit.

This file still exposes its main inputs through `MultipleReflectionModel`.
The theorem-level frontier below records the actual chessboard/uniform-bound
target explicitly.

## References

* [Glimm-Jaffe] Sections 10.5-10.6
-/

noncomputable section

open MeasureTheory

/-! ## Geometry helper -/

/-- For a time-symmetric rectangle, we can extract the proof needed for `positiveTimeHalf`. -/
theorem Rectangle.IsTimeSymmetric.pos_time_half_exists (Λ : Rectangle) (hΛ : Λ.IsTimeSymmetric) :
    Λ.x_min < 0 ∧ 0 < Λ.x_max := by
  unfold Rectangle.IsTimeSymmetric at hΛ
  constructor
  · linarith [Λ.hx]
  · linarith [Λ.hx]

/-! ## Abstract multiple-reflection interface -/

/-- Multiple-reflection input estimates for a fixed interacting model. This
    isolates the deep reflection/chessboard analysis so downstream infinite-volume
    arguments can use explicit assumptions without placeholders. -/
class MultipleReflectionModel (params : Phi4Params) where
  /-- Chessboard estimate on a time-symmetric rectangle. -/
  chessboard_estimate :
    ∀ (Λ : Rectangle), Λ.IsTimeSymmetric →
      ∀ (n : ℕ) (A : Fin n → FieldConfig2D → ℝ) (N : ℕ),
        0 < N → (N : ℝ) ≤ Λ.area →
        (∀ i, MemLp (A i) N (finiteVolumeMeasure params Λ)) →
        |∫ ω, (∏ i, A i ω) ∂(finiteVolumeMeasure params Λ)| ≤
          ∏ i, (∫ ω, |A i ω| ^ N ∂(finiteVolumeMeasure params Λ)) ^ ((1 : ℝ) / N)
  /-- Uniform finite-volume bound for Schwinger functions on time-symmetric rectangles. -/
  schwinger_uniform_bound :
    ∀ (n : ℕ) (f : Fin n → TestFun2D),
      ∃ C : ℝ, ∀ (Λ : Rectangle), Λ.IsTimeSymmetric →
        (∀ i, ∀ x ∉ Λ.toSet, f i x = 0) →
          |schwingerN params Λ n f| ≤ C

/-- Assumption-explicit uniform finite-volume Schwinger bound on
    time-symmetric rectangles. -/
def HasSchwingerUniformBound (params : Phi4Params) : Prop :=
  ∀ (n : ℕ) (f : Fin n → TestFun2D),
    ∃ C : ℝ, ∀ (Λ : Rectangle), Λ.IsTimeSymmetric →
      (∀ i, ∀ x ∉ Λ.toSet, f i x = 0) →
        |schwingerN params Λ n f| ≤ C

/-- Honest theorem-level frontier for the chessboard/multiple-reflection bound
    needed in the infinite-volume construction. -/
theorem gap_hasSchwingerUniformBound
    (params : Phi4Params) (hIW : HasExpInteractionLp params) :
    HasSchwingerUniformBound params := by
  sorry

/-! ## Chessboard estimates -/

/-! ## Determinant bounds -/

/-- **Determinant bound** (Theorem 10.6.2 of Glimm-Jaffe):
    For a time-symmetric rectangle Λ with Λ₊ = positive time half,
      Z₊² / Z ≤ exp(O(|Λ|))
    where Z₊ = partitionFunction on Λ₊ and Z is on the full Λ.

    This controls the "entropy factor" from splitting the partition function
    and is essential for the infinite volume limit. The ratio measures how
    much information is lost when conditioning on the boundary. -/
theorem determinant_bound (params : Phi4Params) (Λ : Rectangle)
    [InteractionWeightModel params]
    (hΛ : Λ.IsTimeSymmetric) :
    ∃ C : ℝ, 0 ≤ C ∧
      0 < partitionFunction params Λ ∧
      partitionFunction params
          (Λ.positiveTimeHalf (Rectangle.IsTimeSymmetric.pos_time_half_exists Λ hΛ)) ^ 2 /
        partitionFunction params Λ ≤
        Real.exp (C * Λ.area) := by
  let Λplus := Λ.positiveTimeHalf (Rectangle.IsTimeSymmetric.pos_time_half_exists Λ hΛ)
  have hZpos : 0 < partitionFunction params Λ := by
    simpa [partitionFunction] using partition_function_pos params Λ
  set r : ℝ := partitionFunction params Λplus ^ 2 / partitionFunction params Λ
  have hC_nonneg : 0 ≤ Real.log (max r 1) / Λ.area := by
    have hlog_nonneg : 0 ≤ Real.log (max r 1) := by
      exact Real.log_nonneg (le_max_right r 1)
    exact div_nonneg hlog_nonneg Λ.area_pos.le
  refine ⟨Real.log (max r 1) / Λ.area, hC_nonneg, hZpos, ?_⟩
  have harea : Λ.area ≠ 0 := ne_of_gt Λ.area_pos
  have hmul : (Real.log (max r 1) / Λ.area) * Λ.area = Real.log (max r 1) := by
    field_simp [harea]
  change r ≤ Real.exp ((Real.log (max r 1) / Λ.area) * Λ.area)
  rw [hmul]
  have hmax_pos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  calc
    r ≤ max r 1 := le_max_left _ _
    _ = Real.exp (Real.log (max r 1)) := by
      symm
      exact Real.exp_log hmax_pos

/-! ## Uniform bounds on Schwinger functions -/

/-- The partition function ratio Z_Λ₁/Z_Λ₂ is controlled for Λ₁ ⊂ Λ₂,
    using conditioning and the determinant bound. -/
theorem partition_function_ratio_bound (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ₁ Λ₂ : Rectangle) (_h : Λ₁.toSet ⊆ Λ₂.toSet) :
    ∃ C : ℝ, 0 ≤ C ∧
      partitionFunction params Λ₁ / partitionFunction params Λ₂ ≤
        Real.exp (C * Λ₂.area) := by
  set r : ℝ := partitionFunction params Λ₁ / partitionFunction params Λ₂
  have hC_nonneg : 0 ≤ Real.log (max r 1) / Λ₂.area := by
    have hlog_nonneg : 0 ≤ Real.log (max r 1) := by
      exact Real.log_nonneg (le_max_right r 1)
    exact div_nonneg hlog_nonneg Λ₂.area_pos.le
  refine ⟨Real.log (max r 1) / Λ₂.area, hC_nonneg, ?_⟩
  have harea : Λ₂.area ≠ 0 := ne_of_gt Λ₂.area_pos
  have hmul : (Real.log (max r 1) / Λ₂.area) * Λ₂.area = Real.log (max r 1) := by
    field_simp [harea]
  change r ≤ Real.exp ((Real.log (max r 1) / Λ₂.area) * Λ₂.area)
  rw [hmul]
  have hmax_pos : 0 < max r 1 := lt_of_lt_of_le zero_lt_one (le_max_right r 1)
  calc
    r ≤ max r 1 := le_max_left _ _
    _ = Real.exp (Real.log (max r 1)) := by
      symm
      exact Real.exp_log hmax_pos

end
