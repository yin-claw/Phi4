/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.UVInfra

/-!
# Shell Estimates for Interaction Analytic Inputs

This file contains the discrete UV-shell analysis: quartic shell decomposition,
pointwise covariance control, the reduced shell-upper function, and the `L²`
convergence chain feeding the limiting interaction.
-/

noncomputable section

open MeasureTheory GaussianField Filter
open scoped ENNReal NNReal

/-! ## UV convergence -/

/-- Under a probability measure, ∫|f| ≤ √(∫ f²) (Jensen / Cauchy-Schwarz). -/
private theorem integral_abs_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : MeasureTheory.Measure Ω} [MeasureTheory.IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Integrable f μ) (hf2 : Integrable (fun ω => f ω ^ 2) μ) :
    ∫ ω, |f ω| ∂μ ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  have h_abs_int := hf.abs
  have h_jensen : (∫ ω, |f ω| ∂μ) ^ 2 ≤ ∫ ω, |f ω| ^ 2 ∂μ := by
    have hconv : ConvexOn ℝ (Set.Ici (0:ℝ)) (fun x : ℝ => x ^ 2) := convexOn_pow 2
    have hcont : ContinuousOn (fun x : ℝ => x ^ 2) (Set.Ici (0:ℝ)) :=
      (continuous_pow 2).continuousOn
    have hclosed : IsClosed (Set.Ici (0:ℝ)) := isClosed_Ici
    have hae : ∀ᵐ x ∂μ, (fun ω => |f ω|) x ∈ Set.Ici (0:ℝ) := by
      filter_upwards with x; exact Set.mem_Ici.mpr (abs_nonneg _)
    have hcomp : Integrable ((fun x : ℝ => x ^ 2) ∘ (fun ω => |f ω|)) μ := by
      show Integrable (fun ω => |f ω| ^ 2) μ
      convert hf2 using 1; ext ω; exact sq_abs (f ω)
    exact hconv.map_integral_le hcont hclosed hae h_abs_int hcomp
  rw [show ∫ ω, |f ω| ^ 2 ∂μ = ∫ ω, f ω ^ 2 ∂μ from by
    congr 1; ext ω; exact sq_abs (f ω)] at h_jensen
  exact Real.le_sqrt_of_sq_le h_jensen

/-- Hölder bridge for the shell `A`-term: `L⁴ × L⁴ → L²` on products.
This is the right reusable norm-level statement after
`wickPower_four_step_decomposition`; the shell estimate for the nonlinear part
reduces to separate `L⁴` bounds on the raw increment and the cubic polynomial
factor. -/
private theorem lpNorm_mul_le_lpNorm_four_mul_four
    {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {f g : α → ℝ}
    (hf : MemLp f 4 μ) (hg : MemLp g 4 μ) :
    lpNorm (fun x => f x * g x) 2 μ ≤ lpNorm f 4 μ * lpNorm g 4 μ := by
  haveI : ENNReal.HolderTriple (4 : ℝ≥0∞) 4 2 := by
    simpa [show (4 : ℝ≥0∞) = 2 * (2 : ℝ≥0∞) by norm_num] using
      (holderTriple_double (2 : ℝ≥0∞))
  have h_e : eLpNorm (fun x => f x * g x) 2 μ ≤ eLpNorm f 4 μ * eLpNorm g 4 μ := by
    have hmul : ∀ x, ‖(fun x1 x2 => x1 * x2) (f x) (g x)‖ ≤ (1 : ℝ) * ‖f x‖ * ‖g x‖ := by
      intro x
      calc
        ‖(fun x1 x2 => x1 * x2) (f x) (g x)‖ ≤ ‖f x‖ * ‖g x‖ := norm_mul_le (f x) (g x)
        _ = (1 : ℝ) * ‖f x‖ * ‖g x‖ := by ring
    simpa using
      (eLpNorm_le_eLpNorm_mul_eLpNorm'_of_norm (μ := μ)
        (p := (4 : ℝ≥0∞)) (q := (4 : ℝ≥0∞)) (r := (2 : ℝ≥0∞))
        hf.1 hg.1 (· * ·) 1 (.of_forall hmul))
  have hfg : MemLp (fun x => f x * g x) (2 : ℝ≥0∞) μ := by
    simpa using (hg.mul' hf)
  rw [← MeasureTheory.toReal_eLpNorm hfg.aestronglyMeasurable]
  rw [← MeasureTheory.toReal_eLpNorm hf.aestronglyMeasurable]
  rw [← MeasureTheory.toReal_eLpNorm hg.aestronglyMeasurable]
  have h_toReal :=
    ENNReal.toReal_mono (ENNReal.mul_ne_top hf.eLpNorm_lt_top.ne hg.eLpNorm_lt_top.ne) h_e
  simpa [ENNReal.toReal_mul] using h_toReal

/-- Exact `L⁴` norm of the raw shell increment. This converts the fourth-moment
identity from `WickProduct` into the norm-level statement needed by the shell
`A`-term estimate. -/
private theorem rawFieldEval_sub_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x)
      4 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)) ^ 2) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let Δ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x
  have hmem : MemLp Δ 4 μ := by
    simpa [Δ, rawFieldEval_sub] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) (4 : ℝ≥0))
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hmem.aestronglyMeasurable]
  norm_num
  have habs4 : ∀ z : ℝ, |z| ^ 4 = z ^ 4 := by
    intro z
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  have habs : ∫ ω : FieldConfig2D, |Δ ω| ^ 4 ∂μ = ∫ ω : FieldConfig2D, (Δ ω) ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact habs4 (Δ ω)
  rw [habs]
  have hfour := rawFieldEval_sub_fourth_expectation mass hmass κ₁ κ₂ x
  exact congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) hfour

/-- Exact `L⁴` norm of a single regularized raw field in terms of its covariance.
This is the basic Gaussian moment formula needed to make the cubic-factor bound
quantitative. -/
private theorem rawFieldEval_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => rawFieldEval mass κ ω x)
      4 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 2) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hX_4 : MemLp X 4 μ := by
    simpa [X, f] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (4 : ℝ≥0))
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hX_4.aestronglyMeasurable]
  norm_num
  have habs4 : ∀ z : ℝ, |z| ^ 4 = z ^ 4 := by
    intro z
    calc
      |z| ^ 4 = (|z| ^ 2) ^ 2 := by ring
      _ = (z ^ 2) ^ 2 := by rw [sq_abs]
      _ = z ^ 4 := by ring
  have habs : ∫ ω : FieldConfig2D, |X ω| ^ 4 ∂μ = ∫ ω : FieldConfig2D, (X ω) ^ 4 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact habs4 (X ω)
  rw [habs]
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  simpa [X, f, σ] using congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) h4

/-- Exact `L⁴` norm of the cubic absolute-value factor `|X|^3` for a Gaussian
raw field `X = rawFieldEval mass κ · x`. This packages the twelfth Gaussian
moment into the norm form needed by `cubic_factor_lpNorm_four_le`. -/
private theorem rawFieldEval_abs_cube_lpNorm_four_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) :
    lpNorm (fun ω : FieldConfig2D => |rawFieldEval mass κ ω x| ^ (3 : ℝ))
      4 (freeFieldMeasure mass hmass)
    = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 6) ^ ((1 : ℝ) / 4) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hX_12 : MemLp X 12 μ := by
    simpa [X, f] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
  have hcube' : MemLp (fun ω => |X ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX_12.norm_rpow_div (3 : ℝ≥0∞)
  have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
    change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
    rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
    norm_num
  have hcube : MemLp (fun ω => |X ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hcube'
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top
    hcube.aestronglyMeasurable]
  norm_num
  have hpow12 : ∀ z : ℝ, (|z| ^ (3 : ℕ)) ^ (4 : ℕ) = z ^ 12 := by
    intro z
    have hsq : |z| ^ 2 = z ^ 2 := by simp
    calc
      (|z| ^ (3 : ℕ)) ^ (4 : ℕ) = |z| ^ (12 : ℕ) := by
        rw [← pow_mul]
      _ = (|z| ^ 2) ^ 6 := by
        rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul]
      _ = (z ^ 2) ^ 6 := by rw [hsq]
      _ = z ^ 12 := by
        rw [show (12 : ℕ) = 2 * 6 by norm_num, pow_mul]
  have habs : ∫ ω : FieldConfig2D, (|X ω| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ =
      ∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards with ω
    exact hpow12 (X ω)
  have habs_pow :
      (∫ ω : FieldConfig2D, (|X ω| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ) ^ ((1 : ℝ) / 4) =
      (∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ) ^ ((1 : ℝ) / 4) := by
    exact congrArg (fun t : ℝ => t ^ ((1 : ℝ) / 4)) habs
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  have h6 : ∫ ω : FieldConfig2D, (ω f) ^ 6 ∂μ = 15 * σ ^ 3 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion_ai mass hmass f 4, h4]
    simp [σ]
    ring
  have h8 : ∫ ω : FieldConfig2D, (ω f) ^ 8 ∂μ = 105 * σ ^ 4 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion_ai mass hmass f 6, h6]
    simp [σ]
    ring
  have h10 : ∫ ω : FieldConfig2D, (ω f) ^ 10 ∂μ = 945 * σ ^ 5 := by
    rw [show (10 : ℕ) = 8 + 2 from rfl, moment_recursion_ai mass hmass f 8, h8]
    simp [σ]
    ring
  have h12 : ∫ ω : FieldConfig2D, (ω f) ^ 12 ∂μ = 10395 * σ ^ 6 := by
    rw [show (12 : ℕ) = 10 + 2 from rfl, moment_recursion_ai mass hmass f 10, h10]
    simp [σ]
    ring
  have hX12 : ∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ = 10395 * σ ^ 6 := by
    simpa [X, f] using h12
  calc
    (∫ x : FieldConfig2D, (|X x| ^ (3 : ℕ)) ^ (4 : ℕ) ∂μ) ^ ((1 : ℝ) / 4) =
        (∫ ω : FieldConfig2D, (X ω) ^ 12 ∂μ) ^ ((1 : ℝ) / 4) := habs_pow
    _ = (10395 * σ ^ 6) ^ ((1 : ℝ) / 4) := by rw [hX12]
    _ = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 6) ^
          ((1 : ℝ) / 4) := by simp [σ]
    _ = (10395 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
          (uvMollifier κ x) (uvMollifier κ x)) ^ 6) ^ ((1 : ℝ) / 4) := by
          simp [f]

/-- Nonnegative mixed cubic terms are controlled by pure cubes.
This is the algebraic inequality behind the `L⁴` bound for the cubic factor in
`wickPower_four_step_decomposition`. -/
private theorem mixed_cubic_le_four_cubes (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    a ^ 3 + a ^ 2 * b + a * b ^ 2 + b ^ 3 ≤ 4 * (a ^ 3 + b ^ 3) := by
  nlinarith [ha, hb, sq_nonneg (a - b)]

/-- Pointwise domination of the cubic factor from
`wickPower_four_step_decomposition` by pure cubic and linear terms in the raw
fields. This avoids estimating the mixed monomials separately. -/
private theorem cubic_factor_pointwise_bound
    (x y c : ℝ) :
    |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 6 * c * (x + y)|
      ≤ 4 * (|x| ^ 3 + |y| ^ 3) + 6 * |c| * (|x| + |y|) := by
  have htri :
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 6 * c * (x + y)|
        ≤ |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3| + |6 * c * (x + y)| := by
    simpa [sub_eq_add_neg] using
      (abs_add_le (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3) (- (6 * c * (x + y))))
  have hpoly1 :
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3|
        ≤ |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3 := by
    calc
      |x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3|
          = |(x ^ 3 + x ^ 2 * y) + (x * y ^ 2 + y ^ 3)| := by ring_nf
      _ ≤ |x ^ 3 + x ^ 2 * y| + |x * y ^ 2 + y ^ 3| := abs_add_le _ _
      _ ≤ (|x ^ 3| + |x ^ 2 * y|) + (|x * y ^ 2| + |y ^ 3|) := by
            gcongr <;> exact abs_add_le _ _
      _ = |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3 := by
            simp [abs_mul, abs_pow, add_assoc, add_left_comm, add_comm]
  have hpoly2 :
      |x| ^ 3 + |x ^ 2 * y| + |x * y ^ 2| + |y| ^ 3
        ≤ 4 * (|x| ^ 3 + |y| ^ 3) := by
    have hxy1 : |x ^ 2 * y| = |x| ^ 2 * |y| := by simp [abs_mul, abs_pow]
    have hxy2 : |x * y ^ 2| = |x| * |y| ^ 2 := by simp [abs_mul, abs_pow]
    rw [hxy1, hxy2]
    exact mixed_cubic_le_four_cubes |x| |y| (abs_nonneg _) (abs_nonneg _)
  have hlin : |6 * c * (x + y)| ≤ 6 * |c| * (|x| + |y|) := by
    calc
      |6 * c * (x + y)| = 6 * |c| * |x + y| := by
        simp [abs_mul, mul_left_comm, mul_comm]
      _ ≤ 6 * |c| * (|x| + |y|) := by
        gcongr
        exact abs_add_le _ _
  exact le_trans htri (by linarith [hpoly1.trans hpoly2, hlin])

/-- `L⁴` bound for the cubic factor in `wickPower_four_step_decomposition`.
This reduces the nonlinear shell term to raw-field `L¹²` and `L⁴` control,
which is available from Gaussian moments. -/
private theorem cubic_factor_lpNorm_four_le
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    lpNorm P 4 μ ≤
      4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ + lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
      6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ + lpNorm (fun ω => |X₁ ω|) 4 μ) := by
  dsimp
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let Q1 : FieldConfig2D → ℝ := fun ω =>
    4 * (|X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ))
  let Q2 : FieldConfig2D → ℝ := fun ω =>
    6 * |c| * (|X₂ ω| + |X₁ ω|)
  have hX1_12 : MemLp X₁ 12 μ := by
    simpa [X₁] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₁ x) (12 : ℝ≥0))
  have hX2_12 : MemLp X₂ 12 μ := by
    simpa [X₂] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x) (12 : ℝ≥0))
  have hX1_4 : MemLp X₁ 4 μ := by
    simpa [X₁] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₁ x) (4 : ℝ≥0))
  have hX2_4 : MemLp X₂ 4 μ := by
    simpa [X₂] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x) (4 : ℝ≥0))
  have hX1_cube' : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX1_12.norm_rpow_div (3 : ℝ≥0∞)
  have hX2_cube' : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
    simpa [Real.norm_eq_abs] using hX2_12.norm_rpow_div (3 : ℝ≥0∞)
  have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
    change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
    rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
    norm_num
  have hX1_cube : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hX1_cube'
  have hX2_cube : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [hdiv12] using hX2_cube'
  have hX1_abs' : MemLp (fun ω => |X₁ ω|) ((4 : ℝ≥0∞) / 1) μ := by
    simpa [Real.norm_eq_abs] using hX1_4.norm_rpow_div (1 : ℝ≥0∞)
  have hX2_abs' : MemLp (fun ω => |X₂ ω|) ((4 : ℝ≥0∞) / 1) μ := by
    simpa [Real.norm_eq_abs] using hX2_4.norm_rpow_div (1 : ℝ≥0∞)
  have hX1_abs : MemLp (fun ω => |X₁ ω|) 4 μ := by
    simpa using hX1_abs'
  have hX2_abs : MemLp (fun ω => |X₂ ω|) 4 μ := by
    simpa using hX2_abs'
  have hQ1_mem : MemLp Q1 4 μ := by
    simpa [Q1] using (hX2_cube.add hX1_cube).const_mul 4
  have hQ2_mem : MemLp Q2 4 μ := by
    simpa [Q2] using (hX2_abs.add hX1_abs).const_mul (6 * |c|)
  have hmono : lpNorm P 4 μ ≤ lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ := by
    apply lpNorm_mono_real (g := fun ω => Q1 ω + Q2 ω)
    · exact hQ1_mem.add hQ2_mem
    · intro ω
      have hω := cubic_factor_pointwise_bound (X₂ ω) (X₁ ω) c
      simpa [P, Q1, Q2] using hω
  have hsum : lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ ≤ lpNorm Q1 4 μ + lpNorm Q2 4 μ :=
    lpNorm_add_le hQ1_mem (g := Q2) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have hQ1 : lpNorm Q1 4 μ =
      4 * lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    simpa [Q1, Pi.smul_apply] using
      lpNorm_const_smul (4 : ℝ)
        (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) μ (p := (4 : ℝ≥0∞))
  have hQ2 : lpNorm Q2 4 μ =
      (6 * |c|) * lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ := by
    simpa [Q2, Pi.smul_apply] using
      lpNorm_const_smul (6 * |c| : ℝ) (fun ω => |X₂ ω| + |X₁ ω|) μ (p := (4 : ℝ≥0∞))
  have hcube_sum :
      lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ ≤
        lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ + lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ :=
    lpNorm_add_le hX2_cube (g := fun ω => |X₁ ω| ^ (3 : ℝ)) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  have habs_sum :
      lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ ≤
        lpNorm (fun ω => |X₂ ω|) 4 μ + lpNorm (fun ω => |X₁ ω|) 4 μ :=
    lpNorm_add_le hX2_abs (g := fun ω => |X₁ ω|) (by norm_num : (1 : ℝ≥0∞) ≤ 4)
  calc
    lpNorm P 4 μ ≤ lpNorm (fun ω => Q1 ω + Q2 ω) 4 μ := hmono
    _ ≤ lpNorm Q1 4 μ + lpNorm Q2 4 μ := hsum
    _ = 4 * lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ)) 4 μ +
          (6 * |c|) * lpNorm (fun ω => |X₂ ω| + |X₁ ω|) 4 μ := by
          rw [hQ1, hQ2]
    _ ≤ 4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := by
          have h1 := mul_le_mul_of_nonneg_left hcube_sum (by positivity : 0 ≤ (4 : ℝ))
          have h2 := mul_le_mul_of_nonneg_left habs_sum (by positivity : 0 ≤ 6 * |c|)
          linarith

/-- Explicit covariance-form version of `cubic_factor_lpNorm_four_le`.
This packages the raw-field `L⁴` / `L¹²` norms into Gaussian moment formulas, so
the remaining work in the shell estimate is genuinely on the covariance side. -/
private theorem cubic_factor_lpNorm_four_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    lpNorm P 4 μ ≤
      4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
      6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  have hbase :
      lpNorm P 4 μ ≤
        4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := by
    simpa [μ, X₁, X₂, c, P] using cubic_factor_lpNorm_four_le mass hmass κ₁ κ₂ x
  have hcube₂ :
      lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ = (10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) := by
    simpa [X₂, σ₂] using rawFieldEval_abs_cube_lpNorm_four_eq mass hmass κ₂ x
  have hcube₁ :
      lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ = (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4) := by
    simpa [X₁, σ₁] using rawFieldEval_abs_cube_lpNorm_four_eq mass hmass κ₁ x
  have habs₂ :
      lpNorm (fun ω => |X₂ ω|) 4 μ = (3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [lpNorm_fun_abs
      ((rawFieldEval_stronglyMeasurable mass κ₂ x).aestronglyMeasurable) (p := (4 : ℝ≥0∞))]
    simpa [X₂, σ₂] using rawFieldEval_lpNorm_four_eq mass hmass κ₂ x
  have habs₁ :
      lpNorm (fun ω => |X₁ ω|) 4 μ = (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4) := by
    rw [lpNorm_fun_abs
      ((rawFieldEval_stronglyMeasurable mass κ₁ x).aestronglyMeasurable) (p := (4 : ℝ≥0∞))]
    simpa [X₁, σ₁] using rawFieldEval_lpNorm_four_eq mass hmass κ₁ x
  calc
    lpNorm P 4 μ ≤
        4 * (lpNorm (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ +
          lpNorm (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ) +
          6 * |c| * (lpNorm (fun ω => |X₂ ω|) 4 μ +
            lpNorm (fun ω => |X₁ ω|) 4 μ) := hbase
    _ = 4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
          rw [hcube₂, hcube₁, habs₂, habs₁]

/-- Square-integrability of the nonlinear `A`-term in the quartic step
decomposition. This is the functional-analytic input needed to integrate the
pointwise bound `(A - B + C)^2 ≤ 3(A^2 + B^2 + C^2)`. -/
private theorem wickPower_four_step_A_sq_integrable
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    Integrable (fun ω => (Δ ω * P ω) ^ 2) μ := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let Q1 : FieldConfig2D → ℝ := fun ω =>
    4 * (|X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ))
  let Q2 : FieldConfig2D → ℝ := fun ω =>
    6 * |c| * (|X₂ ω| + |X₁ ω|)
  let Q : FieldConfig2D → ℝ := fun ω => Q1 ω + Q2 ω
  have hΔ4 : MemLp Δ 4 μ := by
    simpa [Δ, X₁, X₂, rawFieldEval_sub] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) (4 : ℝ≥0))
  have hX1_cube : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₁ x
    have hX1_12 : MemLp X₁ 12 μ := by
      simpa [X₁, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX1_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX2_cube : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₂ x
    have hX2_12 : MemLp X₂ 12 μ := by
      simpa [X₂, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX2_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX1_abs : MemLp (fun ω => |X₁ ω|) 4 μ := by
    simpa [X₁, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₁ x) (4 : ℝ≥0)).abs
  have hX2_abs : MemLp (fun ω => |X₂ ω|) 4 μ := by
    simpa [X₂, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0)).abs
  have hQ1_mem : MemLp Q1 4 μ := by
    simpa [Q1] using (hX2_cube.add hX1_cube).const_mul 4
  have hQ2_mem : MemLp Q2 4 μ := by
    simpa [Q2] using (hX2_abs.add hX1_abs).const_mul (6 * |c|)
  have hQ_mem : MemLp Q 4 μ := by
    exact hQ1_mem.add hQ2_mem
  have hP_meas : AEStronglyMeasurable P μ := by
    let h1 := rawFieldEval_stronglyMeasurable mass κ₁ x
    let h2 := rawFieldEval_stronglyMeasurable mass κ₂ x
    have hP_eq :
        P =
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3)) -
              6 * c * (X₂ ω + X₁ ω)) := by
      funext ω
      simp [P, add_left_comm, add_comm, mul_left_comm, mul_comm]
    have hpoly :
        StronglyMeasurable
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3))) := by
      exact (h2.mul (h1.pow 2)).add ((h1.mul (h2.pow 2)).add ((h1.pow 3).add (h2.pow 3)))
    rw [hP_eq]
    exact (hpoly.sub ((h2.add h1).const_mul (6 * c))).aestronglyMeasurable
  have hP_mem : MemLp P 4 μ := by
    refine MemLp.of_le_mul (c := 1) hQ_mem hP_meas ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hω := cubic_factor_pointwise_bound (X₂ ω) (X₁ ω) c
    have hQ_nonneg : 0 ≤ Q ω := by
      unfold Q Q1 Q2
      positivity
    have hω' : ‖P ω‖ ≤ 1 * ‖Q ω‖ := by
      have hQ_norm : ‖Q ω‖ = Q ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hQ_nonneg]
      calc
        ‖P ω‖ = |P ω| := by simp [Real.norm_eq_abs]
        _ ≤ Q ω := by simpa [P, Q, Q1, Q2] using hω
        _ = ‖Q ω‖ := by rw [hQ_norm]
        _ = 1 * ‖Q ω‖ := by ring
    exact hω'
  have hΔsq_abs : MemLp (fun ω : FieldConfig2D => |Δ ω| ^ (2 : ℝ)) 2 μ := by
    have htmp : MemLp (fun ω : FieldConfig2D => ‖Δ ω‖ ^ (2 : ℝ))
        ((4 : ℝ≥0∞) / 2) μ := by
      simpa [Real.norm_eq_abs] using hΔ4.norm_rpow_div (2 : ℝ≥0∞)
    have hdiv : ((4 : ℝ≥0∞) / 2) = 2 := by
      change (((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)) = ((2 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (4 : NNReal)) (r := (2 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv] using htmp
  have hΔsq : MemLp (fun ω : FieldConfig2D => (Δ ω) ^ 2) 2 μ := by
    refine hΔsq_abs.congr_norm (((rawFieldEval_stronglyMeasurable mass κ₂ x).sub
      (rawFieldEval_stronglyMeasurable mass κ₁ x)).pow 2).aestronglyMeasurable ?_
    filter_upwards with ω
    rw [show |Δ ω| ^ (2 : ℝ) = (Δ ω) ^ 2 by
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
  have hPsq_abs : MemLp (fun ω : FieldConfig2D => |P ω| ^ (2 : ℝ)) 2 μ := by
    have htmp : MemLp (fun ω : FieldConfig2D => ‖P ω‖ ^ (2 : ℝ))
        ((4 : ℝ≥0∞) / 2) μ := by
      simpa [Real.norm_eq_abs] using hP_mem.norm_rpow_div (2 : ℝ≥0∞)
    have hdiv : ((4 : ℝ≥0∞) / 2) = 2 := by
      change (((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)) = ((2 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (4 : NNReal)) (r := (2 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv] using htmp
  have hPsq : MemLp (fun ω : FieldConfig2D => (P ω) ^ 2) 2 μ := by
    refine hPsq_abs.congr_norm (hP_meas.pow 2) ?_
    filter_upwards with ω
    rw [show |P ω| ^ (2 : ℝ) = (P ω) ^ 2 by
      rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
  have hprod_int : Integrable (fun ω : FieldConfig2D => (Δ ω) ^ 2 * (P ω) ^ 2) μ := by
    exact hΔsq.integrable_mul hPsq
  refine hprod_int.congr ?_
  filter_upwards with ω
  ring

/-- Norm-level bound for the nonlinear `A`-term in the quartic step
decomposition. After this theorem, the shell estimate for the nonlinear part is
reduced entirely to covariance quantities. -/
private theorem wickPower_four_step_A_term_lpNorm_two_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    lpNorm (fun ω => Δ ω * P ω) 2 μ ≤
      (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let Δ : FieldConfig2D → ℝ := fun ω => X₂ ω - X₁ ω
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let Q1 : FieldConfig2D → ℝ := fun ω =>
    4 * (|X₂ ω| ^ (3 : ℝ) + |X₁ ω| ^ (3 : ℝ))
  let Q2 : FieldConfig2D → ℝ := fun ω =>
    6 * |c| * (|X₂ ω| + |X₁ ω|)
  let Q : FieldConfig2D → ℝ := fun ω => Q1 ω + Q2 ω
  have hΔ4 : MemLp Δ 4 μ := by
    simpa [Δ, X₁, X₂, rawFieldEval_sub] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) (4 : ℝ≥0))
  have hX1_cube : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₁ x
    have hX1_12 : MemLp X₁ 12 μ := by
      simpa [X₁, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₁ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX1_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX2_cube : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) 4 μ := by
    let f : TestFun2D := uvMollifier κ₂ x
    have hX2_12 : MemLp X₂ 12 μ := by
      simpa [X₂, f] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) f (12 : ℝ≥0))
    have hcube' : MemLp (fun ω => |X₂ ω| ^ (3 : ℝ)) ((12 : ℝ≥0∞) / 3) μ := by
      simpa [Real.norm_eq_abs] using hX2_12.norm_rpow_div (3 : ℝ≥0∞)
    have hdiv12 : ((12 : ℝ≥0∞) / 3) = 4 := by
      change (((12 : NNReal) : ENNReal) / ((3 : NNReal) : ENNReal)) = ((4 : NNReal) : ENNReal)
      rw [← ENNReal.coe_div (p := (12 : NNReal)) (r := (3 : NNReal)) (by norm_num)]
      norm_num
    simpa [hdiv12] using hcube'
  have hX1_abs : MemLp (fun ω => |X₁ ω|) 4 μ := by
    simpa [X₁, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₁ x) (4 : ℝ≥0)).abs
  have hX2_abs : MemLp (fun ω => |X₂ ω|) 4 μ := by
    simpa [X₂, Real.norm_eq_abs] using
      (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0)).abs
  have hQ1_mem : MemLp Q1 4 μ := by
    simpa [Q1] using (hX2_cube.add hX1_cube).const_mul 4
  have hQ2_mem : MemLp Q2 4 μ := by
    simpa [Q2] using (hX2_abs.add hX1_abs).const_mul (6 * |c|)
  have hQ_mem : MemLp Q 4 μ := by
    exact hQ1_mem.add hQ2_mem
  have hP_meas : AEStronglyMeasurable P μ := by
    let h1 := rawFieldEval_stronglyMeasurable mass κ₁ x
    let h2 := rawFieldEval_stronglyMeasurable mass κ₂ x
    have hP_eq :
        P =
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3)) -
              6 * c * (X₂ ω + X₁ ω)) := by
      funext ω
      simp [P, add_left_comm, add_comm, mul_left_comm, mul_comm]
    have hpoly :
        StronglyMeasurable
          (fun ω =>
            X₂ ω * (X₁ ω) ^ 2 + (X₁ ω * (X₂ ω) ^ 2 + ((X₁ ω) ^ 3 + (X₂ ω) ^ 3))) := by
      exact (h2.mul (h1.pow 2)).add ((h1.mul (h2.pow 2)).add ((h1.pow 3).add (h2.pow 3)))
    rw [hP_eq]
    exact (hpoly.sub ((h2.add h1).const_mul (6 * c))).aestronglyMeasurable
  have hP_mem : MemLp P 4 μ := by
    refine MemLp.of_le_mul (c := 1) hQ_mem hP_meas ?_
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hω := cubic_factor_pointwise_bound (X₂ ω) (X₁ ω) c
    have hQ_nonneg : 0 ≤ Q ω := by
      unfold Q Q1 Q2
      positivity
    have hω' : ‖P ω‖ ≤ 1 * ‖Q ω‖ := by
      have hQ_norm : ‖Q ω‖ = Q ω := by
        simp [Real.norm_eq_abs, abs_of_nonneg hQ_nonneg]
      calc
        ‖P ω‖ = |P ω| := by simp [Real.norm_eq_abs]
        _ ≤ Q ω := by simpa [P, Q, Q1, Q2] using hω
        _ = ‖Q ω‖ := by rw [hQ_norm]
        _ = 1 * ‖Q ω‖ := by ring
    exact hω'
  have hprod : lpNorm (fun ω => Δ ω * P ω) 2 μ ≤ lpNorm Δ 4 μ * lpNorm P 4 μ :=
    lpNorm_mul_le_lpNorm_four_mul_four hΔ4 hP_mem
  have hP_bound :
      lpNorm P 4 μ ≤
        4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)) := by
    simpa [μ, X₁, X₂, c, P, σ₁, σ₂] using
      cubic_factor_lpNorm_four_le_covariance mass hmass κ₁ κ₂ x
  have hΔ_eq :
      lpNorm Δ 4 μ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) := by
    simpa [μ, Δ, X₁, X₂, δσ] using rawFieldEval_sub_lpNorm_four_eq mass hmass κ₁ κ₂ x
  calc
    lpNorm (fun ω => Δ ω * P ω) 2 μ ≤ lpNorm Δ 4 μ * lpNorm P 4 μ := hprod
    _ ≤ lpNorm Δ 4 μ *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
          exact mul_le_mul_of_nonneg_left hP_bound MeasureTheory.lpNorm_nonneg
    _ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
        (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
          6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4))) := by
          rw [hΔ_eq]

/-- Exact square expectation of the nonlinear `A`-term in the quartic shell
step, specialized to the UV mollifiers. This is the sharp replacement for the
coarse Hölder route when one wants exact covariance polynomials. -/
private theorem wickPower_four_step_A_term_sq_expectation_exact
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
    let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
    let c := regularizedPointCovariance mass κ₁
    let P : FieldConfig2D → ℝ := fun ω =>
      (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω)
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₂ x)
    ∫ ω : FieldConfig2D, ((X₂ ω - X₁ ω) * P ω) ^ 2 ∂μ =
      105 * σ₂ ^ 4 - 180 * c * σ₂ ^ 3 + 108 * c ^ 2 * σ₂ ^ 2 +
      105 * σ₁ ^ 4 - 180 * c * σ₁ ^ 3 + 108 * c ^ 2 * σ₁ ^ 2 -
      18 * σ₁ ^ 2 * σ₂ ^ 2 - 144 * σ₁ * σ₂ * τ ^ 2 - 48 * τ ^ 4 +
      36 * c * σ₁ * σ₂ ^ 2 + 36 * c * σ₁ ^ 2 * σ₂ +
      144 * c * σ₂ * τ ^ 2 + 144 * c * σ₁ * τ ^ 2 -
      72 * c ^ 2 * σ₁ * σ₂ - 144 * c ^ 2 * τ ^ 2 := by
  let μ := freeFieldMeasure mass hmass
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let c := regularizedPointCovariance mass κ₁
  let P : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
      - 6 * c * (X₂ ω + X₁ ω)
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₂ x)
  have hAeq :
      (fun ω : FieldConfig2D => ((X₂ ω - X₁ ω) * P ω) ^ 2) =
      (fun ω : FieldConfig2D =>
        (wickMonomial 4 c (X₂ ω) - wickMonomial 4 c (X₁ ω)) ^ 2) := by
    funext ω
    symm
    simpa [P] using congrArg (fun t : ℝ => t ^ 2) (wickMonomial_four_diff_factor c (X₂ ω) (X₁ ω))
  dsimp only [μ, X₁, X₂, c, P, σ₁, σ₂, τ]
  rw [hAeq]
  simpa [μ, X₁, X₂, c, σ₁, σ₂, τ, rawFieldEval] using
    (wickMonomial_four_diff_sq_expectation mass hmass (uvMollifier κ₁ x) (uvMollifier κ₂ x) c)

/-- Algebraic normal form for the exact quartic-difference covariance
polynomial, written in terms of the diagonal increment `u = b-a` and shell
variance `d = a+b-2t`. -/
private theorem quartic_diff_covariance_poly_factorized
    (a b t c : ℝ) :
    105 * b ^ 4 - 180 * c * b ^ 3 + 108 * c ^ 2 * b ^ 2 +
      105 * a ^ 4 - 180 * c * a ^ 3 + 108 * c ^ 2 * a ^ 2 -
      18 * a ^ 2 * b ^ 2 - 144 * a * b * t ^ 2 - 48 * t ^ 4 +
      36 * c * a * b ^ 2 + 36 * c * a ^ 2 * b +
      144 * c * b * t ^ 2 + 144 * c * a * t ^ 2 -
      72 * c ^ 2 * a * b - 144 * c ^ 2 * t ^ 2
    =
      (b - a) ^ 2 *
        (12 * (b - a) ^ 2 + 72 * c ^ 2 - 144 * (a + b) * c +
          90 * (a + b) ^ 2 - 18 * (a + b) * (a + b - 2 * t) +
          9 * (a + b - 2 * t) ^ 2)
      +
      (a + b - 2 * t) *
        (30 * (a + b) ^ 3 - 72 * c * (a + b) ^ 2 + 72 * c ^ 2 * (a + b) -
          27 * (a + b) ^ 2 * (a + b - 2 * t) +
          36 * c * (a + b) * (a + b - 2 * t) -
          36 * c ^ 2 * (a + b - 2 * t) +
          12 * (a + b) * (a + b - 2 * t) ^ 2 -
          3 * (a + b - 2 * t) ^ 3) := by
  ring

/-- Under positive semidefiniteness, the diagonal variance increment is
controlled by the shell variance. -/
  private theorem variance_increment_sq_le_two_mul_sum_mul_shell
    {a b t : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht2 : t ^ 2 ≤ a * b) :
    (b - a) ^ 2 ≤ 2 * (a + b) * (a + b - 2 * t) := by
  have habs : t ≤ Real.sqrt (a * b) := by
    by_contra h
    have hsqrt_nonneg : 0 ≤ Real.sqrt (a * b) := Real.sqrt_nonneg _
    have hlt : Real.sqrt (a * b) < t := lt_of_not_ge h
    nlinarith [ht2, Real.sq_sqrt (show 0 ≤ a * b by positivity), hlt]
  have hshell_lb : (Real.sqrt a - Real.sqrt b) ^ 2 ≤ a + b - 2 * t := by
    calc
      (Real.sqrt a - Real.sqrt b) ^ 2
          = a + b - 2 * (Real.sqrt a * Real.sqrt b) := by
              nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
      _ = a + b - 2 * Real.sqrt (a * b) := by
            rw [← Real.sqrt_mul ha b]
      _ ≤ a + b - 2 * t := by linarith
  have hsum_nonneg : 0 ≤ (Real.sqrt a + Real.sqrt b) ^ 2 := sq_nonneg _
  have hsqeq : (b - a) ^ 2 = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    have hprod_eq : (Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b) = a - b := by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
    calc
      (b - a) ^ 2 = (a - b) ^ 2 := by ring
      _ = (((Real.sqrt a - Real.sqrt b) * (Real.sqrt a + Real.sqrt b))) ^ 2 := by rw [hprod_eq]
      _ = (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 := by ring
  rw [hsqeq]
  have hmul :
      (Real.sqrt a - Real.sqrt b) ^ 2 * (Real.sqrt a + Real.sqrt b) ^ 2 ≤
        (a + b - 2 * t) * (Real.sqrt a + Real.sqrt b) ^ 2 := by
    exact mul_le_mul_of_nonneg_right hshell_lb hsum_nonneg
  refine hmul.trans ?_
  have hsum_sq_le : (Real.sqrt a + Real.sqrt b) ^ 2 ≤ 2 * (a + b) := by
    have hsq :
        (Real.sqrt a + Real.sqrt b) ^ 2 = a + b + 2 * (Real.sqrt a * Real.sqrt b) := by
      nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb]
    have hgm : 2 * (Real.sqrt a * Real.sqrt b) ≤ a + b := by
      nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b)]
    linarith
  have hshell_nonneg : 0 ≤ a + b - 2 * t := by
    nlinarith [hshell_lb]
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (mul_le_mul_of_nonneg_left hsum_sq_le hshell_nonneg)

/-- Exact quartic-difference covariance polynomial bounded by the shell
variance times an explicit polynomial in the slow parameters. -/
private theorem quartic_diff_covariance_poly_le_shell
    {a b t c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ht2 : t ^ 2 ≤ a * b) :
    105 * b ^ 4 - 180 * c * b ^ 3 + 108 * c ^ 2 * b ^ 2 +
      105 * a ^ 4 - 180 * c * a ^ 3 + 108 * c ^ 2 * a ^ 2 -
      18 * a ^ 2 * b ^ 2 - 144 * a * b * t ^ 2 - 48 * t ^ 4 +
      36 * c * a * b ^ 2 + 36 * c * a ^ 2 * b +
      144 * c * b * t ^ 2 + 144 * c * a * t ^ 2 -
      72 * c ^ 2 * a * b - 144 * c ^ 2 * t ^ 2
    ≤
      (a + b - 2 * t) *
        (210 * (a + b) ^ 3 + 360 * |c| * (a + b) ^ 2 + 216 * c ^ 2 * (a + b) +
          111 * (a + b) ^ 2 * (a + b - 2 * t) +
          36 * |c| * (a + b) * (a + b - 2 * t) +
          36 * c ^ 2 * (a + b - 2 * t) +
          30 * (a + b) * (a + b - 2 * t) ^ 2 +
          3 * (a + b - 2 * t) ^ 3) := by
  let s := a + b
  let d := a + b - 2 * t
  let u := b - a
  have hu2_le : u ^ 2 ≤ 2 * s * d := by
    simpa [s, d, u] using variance_increment_sq_le_two_mul_sum_mul_shell ha hb ht2
  have hs_nonneg : 0 ≤ s := by
    dsimp [s]
    positivity
  have hd_nonneg : 0 ≤ d := by
    dsimp [d]
    nlinarith [ht2, Real.sq_sqrt (show 0 ≤ a * b by positivity)]
  have hu2_nonneg : 0 ≤ u ^ 2 := sq_nonneg _
  have hQ1 :
      12 * u ^ 2 + 72 * c ^ 2 - 144 * s * c + 90 * s ^ 2 - 18 * s * d + 9 * d ^ 2
      ≤ 72 * c ^ 2 + 144 * s * |c| + 90 * s ^ 2 + 42 * s * d + 9 * d ^ 2 := by
    have hc_abs : c ≤ |c| := le_abs_self c
    have hc_abs' : -c ≤ |c| := neg_le_abs c
    nlinarith [hu2_le, hs_nonneg, hd_nonneg, hc_abs, hc_abs']
  have hQ2 :
      30 * s ^ 3 - 72 * c * s ^ 2 + 72 * c ^ 2 * s - 27 * s ^ 2 * d +
        36 * c * s * d - 36 * c ^ 2 * d + 12 * s * d ^ 2 - 3 * d ^ 3
      ≤ 30 * s ^ 3 + 72 * |c| * s ^ 2 + 72 * c ^ 2 * s + 27 * s ^ 2 * d +
        36 * |c| * s * d + 36 * c ^ 2 * d + 12 * s * d ^ 2 + 3 * d ^ 3 := by
    have hc_abs : c ≤ |c| := le_abs_self c
    have hc_abs' : -c ≤ |c| := neg_le_abs c
    nlinarith [hs_nonneg, hd_nonneg, hc_abs, hc_abs']
  rw [quartic_diff_covariance_poly_factorized]
  have hfirst :
      u ^ 2 *
        (12 * u ^ 2 + 72 * c ^ 2 - 144 * s * c + 90 * s ^ 2 - 18 * s * d + 9 * d ^ 2)
      ≤
      d * (144 * s * c ^ 2 + 288 * s ^ 2 * |c| + 180 * s ^ 3 + 84 * s ^ 2 * d +
        18 * s * d ^ 2) := by
    have h1 :
        u ^ 2 *
          (12 * u ^ 2 + 72 * c ^ 2 - 144 * s * c + 90 * s ^ 2 - 18 * s * d + 9 * d ^ 2)
        ≤
        u ^ 2 * (72 * c ^ 2 + 144 * s * |c| + 90 * s ^ 2 + 42 * s * d + 9 * d ^ 2) := by
      exact mul_le_mul_of_nonneg_left hQ1 hu2_nonneg
    have h2 :
        u ^ 2 * (72 * c ^ 2 + 144 * s * |c| + 90 * s ^ 2 + 42 * s * d + 9 * d ^ 2)
        ≤
        (2 * s * d) * (72 * c ^ 2 + 144 * s * |c| + 90 * s ^ 2 + 42 * s * d + 9 * d ^ 2) := by
      refine mul_le_mul_of_nonneg_right hu2_le ?_
      positivity
    have h3 :
        (2 * s * d) * (72 * c ^ 2 + 144 * s * |c| + 90 * s ^ 2 + 42 * s * d + 9 * d ^ 2)
        = d * (144 * s * c ^ 2 + 288 * s ^ 2 * |c| + 180 * s ^ 3 + 84 * s ^ 2 * d +
          18 * s * d ^ 2) := by
      ring
    exact h1.trans <| by simpa [h3] using h2
  have hsecond :
      d * (30 * s ^ 3 - 72 * c * s ^ 2 + 72 * c ^ 2 * s - 27 * s ^ 2 * d +
        36 * c * s * d - 36 * c ^ 2 * d + 12 * s * d ^ 2 - 3 * d ^ 3)
      ≤
      d * (30 * s ^ 3 + 72 * |c| * s ^ 2 + 72 * c ^ 2 * s + 27 * s ^ 2 * d +
        36 * |c| * s * d + 36 * c ^ 2 * d + 12 * s * d ^ 2 + 3 * d ^ 3) := by
    exact mul_le_mul_of_nonneg_left hQ2 hd_nonneg
  have hsum :
      d * (144 * s * c ^ 2 + 288 * s ^ 2 * |c| + 180 * s ^ 3 + 84 * s ^ 2 * d +
        18 * s * d ^ 2)
      +
      d * (30 * s ^ 3 + 72 * |c| * s ^ 2 + 72 * c ^ 2 * s + 27 * s ^ 2 * d +
        36 * |c| * s * d + 36 * c ^ 2 * d + 12 * s * d ^ 2 + 3 * d ^ 3)
      =
      d *
        (210 * s ^ 3 + 360 * |c| * s ^ 2 + 216 * c ^ 2 * s + 111 * s ^ 2 * d +
          36 * |c| * s * d + 36 * c ^ 2 * d + 30 * s * d ^ 2 + 3 * d ^ 3) := by
    ring
  have := add_le_add hfirst hsecond
  simpa [s, d, u, hsum] using this

/-- The exact `A`-term square expectation depends only on the shell variance
`σ₁ + σ₂ - 2τ` and the diagonal increment `σ₂ - σ₁`. -/
private theorem wickPower_four_step_A_term_sq_expectation_factorized
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₂ x)
    let Δdiag := σ₂ - σ₁
    let δσ := σ₁ + σ₂ - 2 * τ
    let A : FieldConfig2D → ℝ := fun ω =>
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
        ((rawFieldEval mass κ₂ ω x) ^ 3 +
         (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
         rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
         (rawFieldEval mass κ₁ ω x) ^ 3 -
         6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
    ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ =
      Δdiag ^ 2 *
        (12 * Δdiag ^ 2 + 72 * c ^ 2 - 144 * (σ₁ + σ₂) * c +
          90 * (σ₁ + σ₂) ^ 2 - 18 * (σ₁ + σ₂) * δσ + 9 * δσ ^ 2)
      +
      δσ *
        (30 * (σ₁ + σ₂) ^ 3 - 72 * c * (σ₁ + σ₂) ^ 2 + 72 * c ^ 2 * (σ₁ + σ₂) -
          27 * (σ₁ + σ₂) ^ 2 * δσ +
          36 * c * (σ₁ + σ₂) * δσ -
          36 * c ^ 2 * δσ +
          12 * (σ₁ + σ₂) * δσ ^ 2 -
          3 * δσ ^ 3) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₂ x)
  let Δdiag := σ₂ - σ₁
  let δσ := σ₁ + σ₂ - 2 * τ
  let A : FieldConfig2D → ℝ := fun ω =>
    (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
      ((rawFieldEval mass κ₂ ω x) ^ 3 +
       (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
       rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
       (rawFieldEval mass κ₁ ω x) ^ 3 -
       6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
  have hexact :
      ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ =
        105 * σ₂ ^ 4 - 180 * c * σ₂ ^ 3 + 108 * c ^ 2 * σ₂ ^ 2 +
        105 * σ₁ ^ 4 - 180 * c * σ₁ ^ 3 + 108 * c ^ 2 * σ₁ ^ 2 -
        18 * σ₁ ^ 2 * σ₂ ^ 2 - 144 * σ₁ * σ₂ * τ ^ 2 - 48 * τ ^ 4 +
        36 * c * σ₁ * σ₂ ^ 2 + 36 * c * σ₁ ^ 2 * σ₂ +
        144 * c * σ₂ * τ ^ 2 + 144 * c * σ₁ * τ ^ 2 -
        72 * c ^ 2 * σ₁ * σ₂ - 144 * c ^ 2 * τ ^ 2 := by
    simpa [μ, c, σ₁, σ₂, τ, A] using
      wickPower_four_step_A_term_sq_expectation_exact mass hmass κ₁ κ₂ x
  dsimp only [μ, c, σ₁, σ₂, τ, Δdiag, δσ, A]
  rw [hexact]
  simpa [Δdiag, δσ] using quartic_diff_covariance_poly_factorized σ₁ σ₂ τ c

/-- The exact nonlinear `A`-term is controlled by the shell variance `δσ`
times an explicit polynomial in the slow parameters `σ₁ + σ₂`, `|c|`, and
`δσ`. This removes the remaining purely algebraic obstacle on the shell
branch. -/
private theorem wickPower_four_step_A_term_sq_expectation_le_shell
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₂ x)
    let δσ := σ₁ + σ₂ - 2 * τ
    let A : FieldConfig2D → ℝ := fun ω =>
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
        ((rawFieldEval mass κ₂ ω x) ^ 3 +
         (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
         rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
         (rawFieldEval mass κ₁ ω x) ^ 3 -
         6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
    ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
      ≤ δσ *
          (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 + 216 * c ^ 2 * (σ₁ + σ₂) +
            111 * (σ₁ + σ₂) ^ 2 * δσ +
            36 * |c| * (σ₁ + σ₂) * δσ +
            36 * c ^ 2 * δσ +
            30 * (σ₁ + σ₂) * δσ ^ 2 +
            3 * δσ ^ 3) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₂ x)
  let δσ := σ₁ + σ₂ - 2 * τ
  let A : FieldConfig2D → ℝ := fun ω =>
    (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
      ((rawFieldEval mass κ₂ ω x) ^ 3 +
       (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
       rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
       (rawFieldEval mass κ₁ ω x) ^ 3 -
       6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
  have hσ₁ : 0 ≤ σ₁ := by
    simpa [σ₁] using covariance_self_nonneg mass hmass (uvMollifier κ₁ x)
  have hσ₂ : 0 ≤ σ₂ := by
    simpa [σ₂] using covariance_self_nonneg mass hmass (uvMollifier κ₂ x)
  have hτ2 : τ ^ 2 ≤ σ₁ * σ₂ := by
    simpa [σ₁, σ₂, τ] using
      covariance_sq_le_self_mul_self mass hmass (uvMollifier κ₁ x) (uvMollifier κ₂ x)
  calc
    ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
      = 105 * σ₂ ^ 4 - 180 * c * σ₂ ^ 3 + 108 * c ^ 2 * σ₂ ^ 2 +
          105 * σ₁ ^ 4 - 180 * c * σ₁ ^ 3 + 108 * c ^ 2 * σ₁ ^ 2 -
          18 * σ₁ ^ 2 * σ₂ ^ 2 - 144 * σ₁ * σ₂ * τ ^ 2 - 48 * τ ^ 4 +
          36 * c * σ₁ * σ₂ ^ 2 + 36 * c * σ₁ ^ 2 * σ₂ +
          144 * c * σ₂ * τ ^ 2 + 144 * c * σ₁ * τ ^ 2 -
          72 * c ^ 2 * σ₁ * σ₂ - 144 * c ^ 2 * τ ^ 2 := by
            simpa [μ, c, σ₁, σ₂, τ, A] using
              wickPower_four_step_A_term_sq_expectation_exact mass hmass κ₁ κ₂ x
    _ ≤ (σ₁ + σ₂ - 2 * τ) *
          (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 + 216 * c ^ 2 * (σ₁ + σ₂) +
            111 * (σ₁ + σ₂) ^ 2 * (σ₁ + σ₂ - 2 * τ) +
            36 * |c| * (σ₁ + σ₂) * (σ₁ + σ₂ - 2 * τ) +
            36 * c ^ 2 * (σ₁ + σ₂ - 2 * τ) +
            30 * (σ₁ + σ₂) * (σ₁ + σ₂ - 2 * τ) ^ 2 +
            3 * (σ₁ + σ₂ - 2 * τ) ^ 3) := by
              exact quartic_diff_covariance_poly_le_shell hσ₁ hσ₂ hτ2
    _ = δσ *
          (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 + 216 * c ^ 2 * (σ₁ + σ₂) +
            111 * (σ₁ + σ₂) ^ 2 * δσ +
            36 * |c| * (σ₁ + σ₂) * δσ +
            36 * c ^ 2 * δσ +
            30 * (σ₁ + σ₂) * δσ ^ 2 +
            3 * δσ ^ 3) := by
              simp [δσ]

/-- Exact `L²` norm of the quadratic re-Wick factor against a Gaussian raw field.
This isolates the linear renormalization term in the quartic shell increment. -/
private theorem rawFieldEval_rewick_two_lpNorm_two_eq
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D) (c : ℝ) :
    lpNorm (fun ω : FieldConfig2D => wickMonomial 2 c (rawFieldEval mass κ ω x))
      2 (freeFieldMeasure mass hmass)
    = (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ x) (uvMollifier κ x)) ^ 2
        - 2 * c * GaussianField.covariance (freeCovarianceCLM mass hmass)
            (uvMollifier κ x) (uvMollifier κ x)
        + c ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ := freeFieldMeasure mass hmass
  let X : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ ω x
  let f : TestFun2D := uvMollifier κ x
  let σ : ℝ := GaussianField.covariance (freeCovarianceCLM mass hmass) f f
  have hmeas :
      AEStronglyMeasurable (fun ω : FieldConfig2D => wickMonomial 2 c (X ω)) μ := by
    exact ((wickMonomial_continuous 2 c).stronglyMeasurable.comp_measurable
      (rawFieldEval_stronglyMeasurable mass κ x).measurable).aestronglyMeasurable
  rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top hmeas]
  norm_num
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂μ = σ := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => sq (ω f)]
    simpa [GaussianField.covariance, σ] using
      cross_moment_eq_covariance (freeCovarianceCLM mass hmass) f f
  have h4 : ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ = 3 * σ ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion_ai mass hmass f 2, h2]
    simp [σ]
    ring
  have hi4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4) μ :=
    power_integrable_ai mass hmass f 4
  have hi2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2) μ :=
    power_integrable_ai mass hmass f 2
  have hpoly :
      ∀ ω : FieldConfig2D,
        (X ω ^ 2 - c) ^ 2 = (ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2 := by
    intro ω
    change ((ω f) ^ 2 - c) ^ 2 = (ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2
    ring
  simp_rw [hpoly]
  have s1 :
      ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2 + c ^ 2) ∂μ =
        ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2) ∂μ +
        ∫ _ : FieldConfig2D, c ^ 2 ∂μ :=
    integral_add (hi4.sub (hi2.const_mul _)) (integrable_const _)
  have s2 :
      ∫ ω : FieldConfig2D, ((ω f) ^ 4 - 2 * c * (ω f) ^ 2) ∂μ =
        ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂μ -
        ∫ ω : FieldConfig2D, (2 * c * (ω f) ^ 2) ∂μ :=
    integral_sub hi4 (hi2.const_mul _)
  rw [s1, s2, integral_const_mul, integral_const, h4, h2]
  have hμ : μ.real Set.univ = 1 := by
    simp [μ, Measure.real, measure_univ]
  simp [hμ, σ, f]

/-- Covariance-form `L²` norm of the linear re-Wick correction term in the
quartic shell increment. -/
private theorem wickPower_four_step_B_term_lpNorm_two_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun ω : FieldConfig2D =>
      6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)) 2 μ
    = |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  dsimp [μ, c, σ₂, δc]
  let h : FieldConfig2D → ℝ := fun ω =>
    rawFieldEval mass κ₂ ω x ^ 2 - regularizedPointCovariance mass κ₁
  have hscale :
      lpNorm
          ((6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)) • h)
          2 (freeFieldMeasure mass hmass)
        =
          ‖(6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) : ℝ)‖₊ *
            lpNorm h 2 (freeFieldMeasure mass hmass) :=
    MeasureTheory.lpNorm_const_smul _ _ _
  have hrewick :
      lpNorm h 2 (freeFieldMeasure mass hmass)
        =
          (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
              (uvMollifier κ₂ x) (uvMollifier κ₂ x)) ^ 2
            - 2 * regularizedPointCovariance mass κ₁ *
                GaussianField.covariance (freeCovarianceCLM mass hmass)
                  (uvMollifier κ₂ x) (uvMollifier κ₂ x)
            + regularizedPointCovariance mass κ₁ ^ 2) ^ ((1 : ℝ) / 2) := by
    simpa [h, wickMonomial_two] using
      rawFieldEval_rewick_two_lpNorm_two_eq mass hmass κ₂ x (regularizedPointCovariance mass κ₁)
  calc
    lpNorm
        (fun ω : FieldConfig2D =>
          6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
            wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x))
        2 (freeFieldMeasure mass hmass)
      =
        lpNorm
          ((6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)) • h)
          2 (freeFieldMeasure mass hmass) := by
            congr 1
            ext ω
            simp [h, smul_eq_mul, wickMonomial_two]
    _ =
        ‖(6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) : ℝ)‖₊ *
          lpNorm h 2 (freeFieldMeasure mass hmass) := hscale
    _ =
        |6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁)| *
          (3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
              (uvMollifier κ₂ x) (uvMollifier κ₂ x)) ^ 2
            - 2 * regularizedPointCovariance mass κ₁ *
                GaussianField.covariance (freeCovarianceCLM mass hmass)
                  (uvMollifier κ₂ x) (uvMollifier κ₂ x)
            + regularizedPointCovariance mass κ₁ ^ 2) ^ ((1 : ℝ) / 2) := by
              rw [hrewick]
              simp [Real.norm_eq_abs]

/-- Covariance-form `L²` norm of the constant re-Wick correction term in the
  quartic shell increment. -/
private theorem wickPower_four_step_C_term_lpNorm_two_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) :
    let μ := freeFieldMeasure mass hmass
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun _ : FieldConfig2D => 3 * δc ^ 2) 2 μ = |3 * δc ^ 2| := by
  let μ := freeFieldMeasure mass hmass
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  dsimp [μ, δc]
  rw [MeasureTheory.lpNorm_const' (μ := freeFieldMeasure mass hmass) (p := 2)
    (hp₀ := by positivity) (hp := by simp)
    (c := (3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 : ℝ))]
  simp [Real.norm_eq_abs]

/-- Pointwise quadratic bound for the quartic-step decomposition
`(:φ⁴:₂ - :φ⁴:₁) = A - B + C`. This avoids the lossy square-of-a-sum `L²`
estimate and keeps the second-moment analysis at the natural scale. -/
private theorem square_sub_add_const_le_three (a b c : ℝ) :
    (a - b + c) ^ 2 ≤ 3 * (a ^ 2 + b ^ 2 + c ^ 2) := by
  have hnonneg : 0 ≤ (a + b) ^ 2 + (a - c) ^ 2 + (b + c) ^ 2 := by positivity
  nlinarith

/-- Exact square expectation of the linear re-Wick correction term in the
quartic shell increment. -/
private theorem wickPower_four_step_B_term_sq_expectation_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    let B : FieldConfig2D → ℝ := fun ω =>
      6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)
    ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ = (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let B : FieldConfig2D → ℝ := fun ω =>
    6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)
  have hmeas : AEStronglyMeasurable B μ := by
    exact (((wickMonomial_continuous 2 c).stronglyMeasurable.comp_measurable
      (rawFieldEval_stronglyMeasurable mass κ₂ x).measurable).const_mul (6 * δc)).aestronglyMeasurable
  have hnorm :
      lpNorm B 2 μ = |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) := by
    simpa [μ, c, σ₂, δc, B] using
      wickPower_four_step_B_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂ x
  have hlp_sq : lpNorm B 2 μ ^ 2 = ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top hmeas]
    norm_num
    have h_nonneg_int : 0 ≤ ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    rw [show ((∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) =
      Real.sqrt (∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ) by rw [Real.sqrt_eq_rpow]]
    rw [Real.sq_sqrt h_nonneg_int]
  have hrewick_base_nonneg : 0 ≤ 3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2 := by
    nlinarith
  have hrewick_nonneg : 0 ≤ (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← rawFieldEval_rewick_two_lpNorm_two_eq mass hmass κ₂ x c]
    exact MeasureTheory.lpNorm_nonneg
  calc
    ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ = lpNorm B 2 μ ^ 2 := hlp_sq.symm
    _ = (|6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)) ^ 2 := by
          rw [hnorm]
    _ = (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) := by
          rw [sq]
          have habs : |6 * δc| * |6 * δc| = (6 * δc) ^ 2 := by
            rw [← sq_abs, sq]
          have hr :
              (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) *
                  (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
                = 3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2 := by
            by_cases hzero : 3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2 = 0
            · rw [hzero]
              simp
            · have hpos : 0 < 3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2 :=
                lt_of_le_of_ne hrewick_base_nonneg (fun hEq => hzero hEq.symm)
              calc
                (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) *
                    (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
                  = (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ (((1 : ℝ) / 2) + ((1 : ℝ) / 2)) := by
                      rw [← Real.rpow_add hpos]
                _ = 3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2 := by
                      norm_num
          calc
            |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) *
                (|6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2))
              = (|6 * δc| * |6 * δc|) *
                  ((3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2) *
                    (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)) := by
                    ring
            _ = (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) := by
                  rw [habs, hr]

/-- Exact square expectation of the constant re-Wick correction term in the
quartic shell increment. -/
private theorem wickPower_four_step_C_term_sq_expectation_eq_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) :
    let μ := freeFieldMeasure mass hmass
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    let C : FieldConfig2D → ℝ := fun _ => 3 * δc ^ 2
    ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ = (3 * δc ^ 2) ^ 2 := by
  let μ := freeFieldMeasure mass hmass
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let C : FieldConfig2D → ℝ := fun _ => 3 * δc ^ 2
  have hmeas : AEStronglyMeasurable C μ := by
    exact (stronglyMeasurable_const : StronglyMeasurable C).aestronglyMeasurable
  have hnorm : lpNorm C 2 μ = |3 * δc ^ 2| := by
    dsimp [μ, δc, C]
    exact wickPower_four_step_C_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂
  have hlp_sq : lpNorm C 2 μ ^ 2 = ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) ENNReal.ofNat_ne_top hmeas]
    norm_num
    have h_nonneg_int : 0 ≤ ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ :=
      integral_nonneg fun _ => sq_nonneg _
    rw [show ((∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ) ^ ((1 : ℝ) / 2)) =
      Real.sqrt (∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ) by rw [Real.sqrt_eq_rpow]]
    rw [Real.sq_sqrt h_nonneg_int]
  calc
    ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ = lpNorm C 2 μ ^ 2 := hlp_sq.symm
    _ = |3 * δc ^ 2| ^ 2 := by rw [hnorm]
    _ = (3 * δc ^ 2) ^ 2 := by rw [sq_abs]

/-- Pointwise-in-`x` `L²` bound for one quartic Wick-power step. After this
the only remaining obstruction in the shell increment proof is to bound the
covariance expressions uniformly/integrably in `x`. -/
private theorem wickPower_four_step_lpNorm_two_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    lpNorm (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) 2 μ
      ≤
        (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
          (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
            6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
        + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
        + |3 * δc ^ 2| := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let A : FieldConfig2D → ℝ := fun ω =>
    (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
      ((rawFieldEval mass κ₂ ω x) ^ 3 +
       (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
       rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
       (rawFieldEval mass κ₁ ω x) ^ 3 -
       6 * c * (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
  let B : FieldConfig2D → ℝ := fun ω =>
    6 * δc * wickMonomial 2 c (rawFieldEval mass κ₂ ω x)
  let C : FieldConfig2D → ℝ := fun _ => 3 * δc ^ 2
  let h : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x ^ 2 - c
  have hconst_mem : MemLp C 2 μ := by
    simpa [C] using
      (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := (3 * δc ^ 2 : ℝ))
        (by norm_num) (by norm_num)).2
        (by simp)
  have hh_mem : MemLp h 2 μ := by
    have hX4 : MemLp (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x) 4 μ := by
      simpa using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0))
    have hXsq_abs : MemLp (fun ω : FieldConfig2D => |rawFieldEval mass κ₂ ω x| ^ (2 : ℝ)) 2 μ := by
      have htmp : MemLp (fun ω : FieldConfig2D => ‖rawFieldEval mass κ₂ ω x‖ ^ (2 : ℝ))
          ((4 : ℝ≥0∞) / 2) μ := by
        simpa [Real.norm_eq_abs] using hX4.norm_rpow_div (2 : ℝ≥0∞)
      have hdiv : ((4 : ℝ≥0∞) / 2) = 2 := by
        change (((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)) = ((2 : NNReal) : ENNReal)
        rw [← ENNReal.coe_div (p := (4 : NNReal)) (r := (2 : NNReal)) (by norm_num)]
        norm_num
      simpa [hdiv] using htmp
    have hXsq : MemLp (fun ω : FieldConfig2D => rawFieldEval mass κ₂ ω x ^ 2) 2 μ := by
      refine hXsq_abs.congr_norm
        ((rawFieldEval_stronglyMeasurable mass κ₂ x).pow 2).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [show |rawFieldEval mass κ₂ ω x| ^ (2 : ℝ) = rawFieldEval mass κ₂ ω x ^ 2 by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
    have hc_mem : MemLp (fun _ : FieldConfig2D => c) 2 μ := by
      simpa using
        (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := c) (by norm_num) (by norm_num)).2
          (by simp)
    simpa [h] using hXsq.sub hc_mem
  have hB_mem : MemLp B 2 μ := by
    simpa [B, h, wickMonomial_two, smul_eq_mul] using hh_mem.const_mul (6 * δc)
  have hCB_mem : MemLp (fun ω => C ω - B ω) 2 μ := hconst_mem.sub hB_mem
  have hdecomp :
      (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) =
        (fun ω => (C ω - B ω) + A ω) := by
    funext ω
    rw [wickPower_four_step_decomposition mass κ₁ κ₂ ω x]
    simp [A, B, C, c, δc]
    ring
  calc
    lpNorm (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) 2 μ
      = lpNorm (fun ω => (C ω - B ω) + A ω) 2 μ := by rw [hdecomp]
    _ ≤ lpNorm (fun ω => C ω - B ω) 2 μ + lpNorm A 2 μ := by
          exact lpNorm_add_le hCB_mem (g := A) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (lpNorm C 2 μ + lpNorm B 2 μ) + lpNorm A 2 μ := by
          gcongr
          exact lpNorm_sub_le hconst_mem (g := B) (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    _ ≤ (lpNorm C 2 μ
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2))
          + lpNorm A 2 μ := by
            gcongr
            exact le_of_eq <| by simpa [μ, c, σ₂, δc, B] using
              wickPower_four_step_B_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂ x
    _ ≤ (lpNorm C 2 μ
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2))
          + ((3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
            (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
              6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))) := by
            gcongr
            simpa [μ, c, σ₁, σ₂, δσ, A] using
              wickPower_four_step_A_term_lpNorm_two_le_covariance mass hmass κ₁ κ₂ x
    _ = |3 * δc ^ 2|
          + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
          + ((3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
            (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
              6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))) := by
            rw [wickPower_four_step_C_term_lpNorm_two_eq_covariance mass hmass κ₁ κ₂]
    _ = (3 * δσ ^ 2) ^ ((1 : ℝ) / 4) *
          (4 * ((10395 * σ₂ ^ 6) ^ ((1 : ℝ) / 4) + (10395 * σ₁ ^ 6) ^ ((1 : ℝ) / 4)) +
            6 * |c| * ((3 * σ₂ ^ 2) ^ ((1 : ℝ) / 4) + (3 * σ₁ ^ 2) ^ ((1 : ℝ) / 4)))
        + |6 * δc| * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) ^ ((1 : ℝ) / 2)
        + |3 * δc ^ 2| := by ring

/-- The square of the Wick-step difference is integrable on the product of the
free field measure with Lebesgue measure restricted to `Λ`. This is a purely
functional-analytic bridge: the pointwise inequality `(a - b)^2 ≤ 2(a^2 + b^2)`
reduces integrability to the already-proved product-square integrability of the
individual cutoff Wick powers. -/
private theorem wickPower_step_sq_integrable_prod (params : Phi4Params) (Λ : Rectangle)
    (κ₁ κ₂ : UVCutoff) :
    Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      ((freeFieldMeasure params.mass params.mass_pos).prod
        (MeasureTheory.volume.restrict Λ.toSet)) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  have hmeas : AEStronglyMeasurable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2 - wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      (μ.prod ν) := by
    exact (((wickPower_stronglyMeasurable_uncurry 4 params.mass κ₂).sub
      (wickPower_stronglyMeasurable_uncurry 4 params.mass κ₁)).pow 2).aestronglyMeasurable
  have hκ₂ := wickPower_sq_integrable_prod params Λ κ₂
  have hκ₁ := wickPower_sq_integrable_prod params Λ κ₁
  have hsum : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        (wickPower 4 params.mass κ₂ p.1 p.2) ^ 2 +
          (wickPower 4 params.mass κ₁ p.1 p.2) ^ 2)
      (μ.prod ν) := hκ₂.add hκ₁
  have hdom : Integrable
      (fun p : FieldConfig2D × Spacetime2D =>
        2 * ((wickPower 4 params.mass κ₂ p.1 p.2) ^ 2 +
          (wickPower 4 params.mass κ₁ p.1 p.2) ^ 2))
      (μ.prod ν) := hsum.const_mul 2
  apply hdom.mono hmeas
  filter_upwards with p
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  rw [Real.norm_of_nonneg (by positivity)]
  nlinarith [sq_nonneg
    (wickPower 4 params.mass κ₂ p.1 p.2 + wickPower 4 params.mass κ₁ p.1 p.2)]

/-- Spatial bridge from the pointwise Wick-step square to the cutoff interaction
increment. This isolates the remaining shell-rate theorem to a covariance bound
under the spatial integral: all Fubini and Cauchy-Schwarz bookkeeping is done
here. -/
private theorem interactionCutoff_sub_sq_le_spatialIntegral
    (params : Phi4Params) (Λ : Rectangle) (κ₁ κ₂ : UVCutoff) :
    ∫ ω : FieldConfig2D,
      (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x) ^ 2
                ∂(freeFieldMeasure params.mass params.mass_pos) := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  let ν := MeasureTheory.volume.restrict Λ.toSet
  let d : FieldConfig2D → Spacetime2D → ℝ := fun ω x =>
    wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x
  have hprod : Integrable (fun p : FieldConfig2D × Spacetime2D => (d p.1 p.2) ^ 2) (μ.prod ν) := by
    simpa [μ, ν, d] using wickPower_step_sq_integrable_prod params Λ κ₁ κ₂
  have hdint : Integrable (fun ω => ∫ x, (d ω x) ^ 2 ∂ν) μ :=
    hprod.integral_prod_left
  have hdom :
      Integrable (fun ω => (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
        ∫ x, (d ω x) ^ 2 ∂ν) μ := hdint.const_mul _
  have hnonneg :
      0 ≤ᵐ[μ] fun ω : FieldConfig2D =>
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 :=
    Filter.Eventually.of_forall fun _ => sq_nonneg _
  have hpoint :
      ∀ᵐ ω ∂μ,
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 ≤
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    have hκ₂_int : Integrable (fun x => wickPower 4 params.mass κ₂ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₂ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hκ₁_int : Integrable (fun x => wickPower 4 params.mass κ₁ ω x) ν :=
      (wickPower_continuous_in_x 4 params.mass κ₁ ω).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hd_int : Integrable (fun x => d ω x) ν := hκ₂_int.sub hκ₁_int
    have hd_sq_int : Integrable (fun x => (d ω x) ^ 2) ν := by
      exact (((wickPower_continuous_in_x 4 params.mass κ₂ ω).sub
        (wickPower_continuous_in_x 4 params.mass κ₁ ω)).pow 2).continuousOn.integrableOn_compact
        Λ.toSet_isCompact
    have hsub :
        interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω =
          params.coupling * ∫ x in Λ.toSet, d ω x := by
      unfold interactionCutoff
      rw [← mul_sub_left_distrib]
      congr 1
      rw [integral_sub hκ₂_int hκ₁_int]
    calc
      (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2
        = params.coupling ^ 2 * (∫ x in Λ.toSet, d ω x) ^ 2 := by
            rw [hsub, mul_pow]
      _ ≤ params.coupling ^ 2 *
            ((MeasureTheory.volume Λ.toSet).toReal * ∫ x in Λ.toSet, (d ω x) ^ 2) := by
            gcongr
            exact sq_setIntegral_le_volume_mul_setIntegral_sq
              Λ.toSet Λ.toSet_measurableSet hd_int hd_sq_int Λ.toSet_volume_ne_top
      _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν := by
            rw [mul_assoc]
  have hle := integral_mono_of_nonneg hnonneg hdom hpoint
  calc
    ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ κ₂ ω - interactionCutoff params Λ κ₁ ω) ^ 2 ∂μ
      ≤ ∫ ω : FieldConfig2D,
          (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
            ∫ x, (d ω x) ^ 2 ∂ν ∂μ := hle
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ ω : FieldConfig2D, ∫ x, (d ω x) ^ 2 ∂ν ∂μ := by
          rw [integral_const_mul]
    _ = (params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal) *
          ∫ x, ∫ ω : FieldConfig2D, (d ω x) ^ 2 ∂μ ∂ν := by
          congr 1
          exact MeasureTheory.integral_integral_swap hprod
    _ = params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass κ₂ ω x - wickPower 4 params.mass κ₁ ω x) ^ 2 ∂μ := by
          rfl

/-- Pointwise square-expectation bound for a quartic Wick-power step, obtained
directly from the decomposition `(:φ⁴:₂ - :φ⁴:₁) = A - B + C` and the exact
second-moment formulas for the three pieces. This is sharper than squaring the
`L²` norm bound and isolates the genuine remaining shell-rate problem in the
covariance expressions. -/
private theorem wickPower_four_step_sq_expectation_le_covariance
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    let μ := freeFieldMeasure mass hmass
    let c := regularizedPointCovariance mass κ₁
    let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
    let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
    let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
    let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
    ∫ ω : FieldConfig2D,
      (wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) ^ 2 ∂μ
      ≤
        3 *
          (δσ *
              (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 +
                216 * c ^ 2 * (σ₁ + σ₂) + 111 * (σ₁ + σ₂) ^ 2 * δσ +
                36 * |c| * (σ₁ + σ₂) * δσ + 36 * c ^ 2 * δσ +
                30 * (σ₁ + σ₂) * δσ ^ 2 + 3 * δσ ^ 3)
            + (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2)
            + (3 * δc ^ 2) ^ 2) := by
  let μ := freeFieldMeasure mass hmass
  let c := regularizedPointCovariance mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let τ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₁ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM mass hmass)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁
  let X₁ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₁ ω x
  let X₂ : FieldConfig2D → ℝ := fun ω => rawFieldEval mass κ₂ ω x
  let A : FieldConfig2D → ℝ := fun ω =>
    (X₂ ω - X₁ ω) *
      ((X₂ ω) ^ 3 + (X₂ ω) ^ 2 * X₁ ω + X₂ ω * (X₁ ω) ^ 2 + (X₁ ω) ^ 3
        - 6 * c * (X₂ ω + X₁ ω))
  let B : FieldConfig2D → ℝ := fun ω =>
    6 * δc * wickMonomial 2 c (X₂ ω)
  let C : FieldConfig2D → ℝ := fun _ => 3 * δc ^ 2
  let h : FieldConfig2D → ℝ := fun ω =>
    wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x
  have hκ₂_mem : MemLp (fun ω : FieldConfig2D => wickPower 4 mass κ₂ ω x) 2 μ := by
    simpa [μ] using
      (wickPower_memLp 4 mass hmass κ₂ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hκ₁_mem : MemLp (fun ω : FieldConfig2D => wickPower 4 mass κ₁ ω x) 2 μ := by
    simpa [μ] using
      (wickPower_memLp 4 mass hmass κ₁ x (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
  have hh_mem : MemLp h 2 μ := by
    simpa [h] using hκ₂_mem.sub hκ₁_mem
  let q : FieldConfig2D → ℝ := fun ω => X₂ ω ^ 2 - c
  have hq_mem : MemLp q 2 μ := by
    have hX4 : MemLp X₂ 4 μ := by
      simpa [X₂] using
        (GaussianField.pairing_memLp (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (4 : ℝ≥0))
    have hXsq_abs : MemLp (fun ω : FieldConfig2D => |X₂ ω| ^ (2 : ℝ)) 2 μ := by
      have htmp : MemLp (fun ω : FieldConfig2D => ‖X₂ ω‖ ^ (2 : ℝ))
          ((4 : ℝ≥0∞) / 2) μ := by
        simpa [Real.norm_eq_abs] using hX4.norm_rpow_div (2 : ℝ≥0∞)
      have hdiv : ((4 : ℝ≥0∞) / 2) = 2 := by
        change (((4 : NNReal) : ENNReal) / ((2 : NNReal) : ENNReal)) = ((2 : NNReal) : ENNReal)
        rw [← ENNReal.coe_div (p := (4 : NNReal)) (r := (2 : NNReal)) (by norm_num)]
        norm_num
      simpa [hdiv] using htmp
    have hXsq : MemLp (fun ω : FieldConfig2D => X₂ ω ^ 2) 2 μ := by
      refine hXsq_abs.congr_norm ((rawFieldEval_stronglyMeasurable mass κ₂ x).pow 2).aestronglyMeasurable ?_
      filter_upwards with ω
      rw [show |X₂ ω| ^ (2 : ℝ) = X₂ ω ^ 2 by
        rw [show (2 : ℝ) = (2 : ℕ) by norm_num, Real.rpow_natCast, sq_abs]]
    have hc_mem : MemLp (fun _ : FieldConfig2D => c) 2 μ := by
      simpa using
        (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := c) (by norm_num) (by norm_num)).2
          (by simp)
    simpa [q] using hXsq.sub hc_mem
  have hB_mem : MemLp B 2 μ := by
    simpa [B, q, wickMonomial_two, smul_eq_mul] using hq_mem.const_mul (6 * δc)
  have hC_mem : MemLp C 2 μ := by
    simpa [C] using
      (memLp_const_iff (μ := μ) (p := (2 : ℝ≥0∞)) (c := (3 * δc ^ 2 : ℝ))
        (by norm_num) (by norm_num)).2
        (by simp)
  have hstep_sq_int : Integrable (fun ω : FieldConfig2D => (h ω) ^ 2) μ := hh_mem.integrable_sq
  have hA_sq_int : Integrable (fun ω : FieldConfig2D => (A ω) ^ 2) μ := by
    simpa [μ, X₁, X₂, c, A] using
      wickPower_four_step_A_sq_integrable mass hmass κ₁ κ₂ x
  have hB_sq_int : Integrable (fun ω : FieldConfig2D => (B ω) ^ 2) μ := hB_mem.integrable_sq
  have hC_sq_int : Integrable (fun ω : FieldConfig2D => (C ω) ^ 2) μ := hC_mem.integrable_sq
  have hR_int :
      Integrable (fun ω : FieldConfig2D => 3 * ((A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2)) μ := by
    simpa [mul_add, add_assoc, add_left_comm, add_comm] using
      ((hA_sq_int.add hB_sq_int).add hC_sq_int).const_mul 3
  have hdecomp : ∀ ω : FieldConfig2D, h ω = A ω - B ω + C ω := by
    intro ω
    simp [h, A, B, C, X₁, X₂, c, δc, wickPower_four_step_decomposition mass κ₁ κ₂ ω x]
  have hpointwise :
      (fun ω : FieldConfig2D => (h ω) ^ 2)
        ≤ᵐ[μ] fun ω => 3 * ((A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2) := by
    refine Filter.Eventually.of_forall ?_
    intro ω
    simpa [hdecomp ω] using square_sub_add_const_le_three (A ω) (B ω) (C ω)
  have hmono :
      ∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ
        ≤ ∫ ω : FieldConfig2D, 3 * ((A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2) ∂μ := by
    exact integral_mono_ae hstep_sq_int hR_int hpointwise
  have hsum :
      ∫ ω : FieldConfig2D, ((A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2) ∂μ
        = ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
          + ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ
          + ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ := by
    calc
      ∫ ω : FieldConfig2D, (A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2 ∂μ
        = ∫ ω : FieldConfig2D, (A ω) ^ 2 + (B ω) ^ 2 ∂μ
            + ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ := by
              simpa [add_assoc] using integral_add (hA_sq_int.add hB_sq_int) hC_sq_int
      _ = (∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
            + ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ)
            + ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ := by
              rw [integral_add hA_sq_int hB_sq_int]
  have hδσ_eq : δσ = σ₁ + σ₂ - 2 * τ := by
    dsimp [δσ, σ₁, σ₂, τ]
    have hcomm :
        GaussianField.covariance (freeCovarianceCLM mass hmass) (uvMollifier κ₂ x) (uvMollifier κ₁ x)
          = GaussianField.covariance (freeCovarianceCLM mass hmass) (uvMollifier κ₁ x) (uvMollifier κ₂ x) := by
      simp [GaussianField.covariance, real_inner_comm]
    rw [covariance_sub_self mass hmass (uvMollifier κ₂ x) (uvMollifier κ₁ x), hcomm]
    ring
  have hB_eq :
      ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ
        = (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2) := by
    simpa [μ, c, σ₂, δc, B, X₂, wickMonomial_two, smul_eq_mul] using
      wickPower_four_step_B_term_sq_expectation_eq_covariance mass hmass κ₁ κ₂ x
  have hC_eq :
      ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ = (3 * δc ^ 2) ^ 2 := by
    have hC_eq_raw := wickPower_four_step_C_term_sq_expectation_eq_covariance mass hmass κ₁ κ₂
    dsimp [μ, δc, C] at hC_eq_raw ⊢
    exact hC_eq_raw
  have hA_bound :
      ∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
        ≤
          δσ *
            (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 +
              216 * c ^ 2 * (σ₁ + σ₂) + 111 * (σ₁ + σ₂) ^ 2 * δσ +
              36 * |c| * (σ₁ + σ₂) * δσ + 36 * c ^ 2 * δσ +
              30 * (σ₁ + σ₂) * δσ ^ 2 + 3 * δσ ^ 3) := by
    rw [hδσ_eq]
    simpa [μ, c, σ₁, σ₂, τ, A] using
      wickPower_four_step_A_term_sq_expectation_le_shell mass hmass κ₁ κ₂ x
  simpa [μ, c, σ₁, σ₂, δσ, δc] using
    (calc
      ∫ ω : FieldConfig2D, (wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x) ^ 2 ∂μ
        = ∫ ω : FieldConfig2D, (h ω) ^ 2 ∂μ := by rfl
      _ ≤ ∫ ω : FieldConfig2D, 3 * ((A ω) ^ 2 + (B ω) ^ 2 + (C ω) ^ 2) ∂μ := hmono
      _ = 3 *
            (∫ ω : FieldConfig2D, (A ω) ^ 2 ∂μ
              + ∫ ω : FieldConfig2D, (B ω) ^ 2 ∂μ
              + ∫ ω : FieldConfig2D, (C ω) ^ 2 ∂μ) := by
            rw [integral_const_mul, hsum]
      _ ≤
          3 *
            (δσ *
                (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 +
                  216 * c ^ 2 * (σ₁ + σ₂) + 111 * (σ₁ + σ₂) ^ 2 * δσ +
                  36 * |c| * (σ₁ + σ₂) * δσ + 36 * c ^ 2 * δσ +
                  30 * (σ₁ + σ₂) * δσ ^ 2 + 3 * δσ ^ 3)
              + (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2)
              + (3 * δc ^ 2) ^ 2) := by
            rw [hB_eq, hC_eq]
            gcongr)

/-- The exact covariance-control upper function for one standard-sequence quartic
UV shell step.

This packages the fully reduced pointwise second-moment estimate for
`wickPower 4 params.mass (standardUVCutoffSeq (n+1)) - wickPower 4 params.mass (standardUVCutoffSeq n)`.
After the A/B/C split and the Gaussian moment algebra, the remaining shell
problem is precisely to control the spatial integral of this nonnegative
function. -/
def wickPowerStandardSeqShellUpper
    (params : Phi4Params) (n : ℕ) (x : Spacetime2D) : ℝ :=
  let κ₁ := standardUVCutoffSeq n
  let κ₂ := standardUVCutoffSeq (n + 1)
  let c := regularizedPointCovariance params.mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance params.mass κ₂ - regularizedPointCovariance params.mass κ₁
  3 *
    (δσ *
        (210 * (σ₁ + σ₂) ^ 3 + 360 * |c| * (σ₁ + σ₂) ^ 2 +
          216 * c ^ 2 * (σ₁ + σ₂) + 111 * (σ₁ + σ₂) ^ 2 * δσ +
          36 * |c| * (σ₁ + σ₂) * δσ + 36 * c ^ 2 * δσ +
          30 * (σ₁ + σ₂) * δσ ^ 2 + 3 * δσ ^ 3)
      + (6 * δc) ^ 2 * (3 * σ₂ ^ 2 - 2 * c * σ₂ + c ^ 2)
      + (3 * δc ^ 2) ^ 2)

/-- Continuity of the reduced shell-upper function. This is purely local
covariance algebra: the remaining open shell theorem is about its spatial size,
not about measurability or compact-set integrability. -/
private theorem continuous_wickPowerStandardSeqShellUpper
    (params : Phi4Params) (n : ℕ) :
    Continuous (wickPowerStandardSeqShellUpper params n) := by
  let κ₁ := standardUVCutoffSeq n
  let κ₂ := standardUVCutoffSeq (n + 1)
  let c : ℝ := regularizedPointCovariance params.mass κ₁
  let δc : ℝ := regularizedPointCovariance params.mass κ₂ - regularizedPointCovariance params.mass κ₁
  let σ₁ : Spacetime2D → ℝ := fun x =>
    GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
      (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ : Spacetime2D → ℝ := fun x =>
    GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
      (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ : Spacetime2D → ℝ := fun x =>
    GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
  have hσ₁ : Continuous σ₁ := by
    simpa [σ₁] using
      continuous_covariance_comp
        (freeCovarianceCLM params.mass params.mass_pos)
        (gap_uvMollifier_continuous κ₁) (gap_uvMollifier_continuous κ₁)
  have hσ₂ : Continuous σ₂ := by
    simpa [σ₂] using
      continuous_covariance_comp
        (freeCovarianceCLM params.mass params.mass_pos)
        (gap_uvMollifier_continuous κ₂) (gap_uvMollifier_continuous κ₂)
  have hδσ : Continuous δσ := by
    simpa [δσ] using
      continuous_covariance_comp
        (freeCovarianceCLM params.mass params.mass_pos)
        ((gap_uvMollifier_continuous κ₂).sub (gap_uvMollifier_continuous κ₁))
        ((gap_uvMollifier_continuous κ₂).sub (gap_uvMollifier_continuous κ₁))
  have hcont :
      Continuous fun x : Spacetime2D =>
        3 *
          (δσ x *
              (210 * (σ₁ x + σ₂ x) ^ 3 + 360 * |c| * (σ₁ x + σ₂ x) ^ 2 +
                216 * c ^ 2 * (σ₁ x + σ₂ x) + 111 * (σ₁ x + σ₂ x) ^ 2 * δσ x +
                36 * |c| * (σ₁ x + σ₂ x) * δσ x + 36 * c ^ 2 * δσ x +
                30 * (σ₁ x + σ₂ x) * δσ x ^ 2 + 3 * δσ x ^ 3)
            + (6 * δc) ^ 2 * (3 * σ₂ x ^ 2 - 2 * c * σ₂ x + c ^ 2)
            + (3 * δc ^ 2) ^ 2) := by
    continuity
  simpa [wickPowerStandardSeqShellUpper, κ₁, κ₂, c, δc, σ₁, σ₂, δσ] using hcont

/-- Compact-set integrability of the reduced shell-upper function. -/
private theorem integrable_wickPowerStandardSeqShellUpper
    (params : Phi4Params) (n : ℕ) (Λ : Rectangle) :
    Integrable (fun x => wickPowerStandardSeqShellUpper params n x)
      (MeasureTheory.volume.restrict Λ.toSet) := by
  simpa [MeasureTheory.IntegrableOn] using
    (continuous_wickPowerStandardSeqShellUpper params n).continuousOn.integrableOn_compact
      Λ.toSet_isCompact

set_option maxHeartbeats 800000 in
private theorem shell_upper_poly_le_of_bounds
    {S Delta c sigSum sig2 dSig dC : ℝ}
    (hS0 : 0 ≤ S) (hS1 : 1 ≤ S)
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1)
    (hsigSum0 : 0 ≤ sigSum) (hsig20 : 0 ≤ sig2) (hdSig0 : 0 ≤ dSig)
    (hc : |c| ≤ S) (hsigSum : sigSum ≤ S) (hsig2 : sig2 ≤ S)
    (hdSig : dSig ≤ Delta) (hdC : |dC| ≤ Delta) :
    3 *
      (dSig *
          (210 * sigSum ^ 3 + 360 * |c| * sigSum ^ 2 +
            216 * c ^ 2 * sigSum + 111 * sigSum ^ 2 * dSig +
            36 * |c| * sigSum * dSig + 36 * c ^ 2 * dSig +
            30 * sigSum * dSig ^ 2 + 3 * dSig ^ 3)
        + (6 * dC) ^ 2 * (3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2)
        + (3 * dC ^ 2) ^ 2)
      ≤ 3681 * Delta * S ^ 3 := by
  have hdC_sq : dC ^ 2 ≤ Delta ^ 2 := by
    have habs_sq : |dC| * |dC| ≤ Delta * Delta := by gcongr
    simpa [sq, sq_abs] using habs_sq
  have hc_sq : c ^ 2 ≤ S ^ 2 := by
    have habs_sq : |c| * |c| ≤ S * S := by gcongr
    simpa [sq, sq_abs] using habs_sq
  have hsigSum_sq : sigSum ^ 2 ≤ S ^ 2 := by
    nlinarith [hsigSum, sq_nonneg sigSum, sq_nonneg S]
  have hsigSum_cube : sigSum ^ 3 ≤ S ^ 3 := by
    nlinarith [hsigSum, hsigSum_sq, hS0]
  have hsig2_sq : sig2 ^ 2 ≤ S ^ 2 := by
    nlinarith [hsig2, sq_nonneg sig2, sq_nonneg S]
  have hdSig_sq : dSig ^ 2 ≤ Delta ^ 2 := by
    nlinarith [hdSig, sq_nonneg dSig, sq_nonneg Delta]
  have hdSig_cube : dSig ^ 3 ≤ Delta ^ 3 := by
    nlinarith [hdSig, hdSig_sq, hDelta0]
  have hA_inner :
      dSig *
        (210 * sigSum ^ 3 + 360 * |c| * sigSum ^ 2 + 216 * c ^ 2 * sigSum +
          111 * sigSum ^ 2 * dSig + 36 * |c| * sigSum * dSig + 36 * c ^ 2 * dSig +
          30 * sigSum * dSig ^ 2 + 3 * dSig ^ 3)
      ≤ Delta * (786 * S ^ 3 + 183 * S ^ 2 * Delta + 30 * S * Delta ^ 2 + 3 * Delta ^ 3) := by
    have h1 : 210 * sigSum ^ 3 ≤ 210 * S ^ 3 := by gcongr
    have h2 : 360 * |c| * sigSum ^ 2 ≤ 360 * S * S ^ 2 := by gcongr
    have h3 : 216 * c ^ 2 * sigSum ≤ 216 * S ^ 2 * S := by gcongr
    have h4 : 111 * sigSum ^ 2 * dSig ≤ 111 * S ^ 2 * Delta := by gcongr
    have h5 : 36 * |c| * sigSum * dSig ≤ 36 * S * S * Delta := by gcongr
    have h6 : 36 * c ^ 2 * dSig ≤ 36 * S ^ 2 * Delta := by gcongr
    have h7 : 30 * sigSum * dSig ^ 2 ≤ 30 * S * Delta ^ 2 := by gcongr
    have h8 : 3 * dSig ^ 3 ≤ 3 * Delta ^ 3 := by gcongr
    have hsum :
        210 * sigSum ^ 3 + 360 * |c| * sigSum ^ 2 + 216 * c ^ 2 * sigSum +
          111 * sigSum ^ 2 * dSig + 36 * |c| * sigSum * dSig + 36 * c ^ 2 * dSig +
          30 * sigSum * dSig ^ 2 + 3 * dSig ^ 3
        ≤ 786 * S ^ 3 + 183 * S ^ 2 * Delta + 30 * S * Delta ^ 2 + 3 * Delta ^ 3 := by
      nlinarith [h1, h2, h3, h4, h5, h6, h7, h8]
    gcongr
  have hcSig2_abs : |c * sig2| ≤ S * S := by
    rw [abs_mul, abs_of_nonneg hsig20]
    gcongr
  have hcross : -2 * c * sig2 ≤ 2 * S ^ 2 := by
    nlinarith [hcSig2_abs]
  have hB_quad_nonneg : 0 ≤ 3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2 := by
    have : 3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2 = (sig2 - c) ^ 2 + 2 * sig2 ^ 2 := by ring
    rw [this]
    positivity
  have hB_quad : 3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2 ≤ 6 * S ^ 2 := by
    nlinarith [hsig2_sq, hc_sq, hcross]
  have hB_inner : (6 * dC) ^ 2 * (3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2) ≤ 216 * Delta ^ 2 * S ^ 2 := by
    have hdC4 : (6 * dC) ^ 2 ≤ (6 * Delta) ^ 2 := by
      nlinarith [hdC_sq, sq_nonneg Delta]
    calc
      (6 * dC) ^ 2 * (3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2)
          ≤ (6 * Delta) ^ 2 * (6 * S ^ 2) := by gcongr
      _ = 216 * Delta ^ 2 * S ^ 2 := by ring
  have hC_inner : (3 * dC ^ 2) ^ 2 ≤ 9 * Delta ^ 4 := by
    calc
      (3 * dC ^ 2) ^ 2 = 9 * (dC ^ 2) ^ 2 := by ring
      _ ≤ 9 * (Delta ^ 2) ^ 2 := by gcongr
      _ = 9 * Delta ^ 4 := by ring
  have h_dom1 : Delta ^ 2 * S ^ 2 ≤ Delta * S ^ 3 := by
    have hD2 : Delta ^ 2 ≤ Delta := by nlinarith
    have hS2 : S ^ 2 ≤ S ^ 3 := by nlinarith
    nlinarith
  have h_dom2 : Delta ^ 3 * S ≤ Delta * S ^ 3 := by
    have hD3 : Delta ^ 3 ≤ Delta := by nlinarith
    have hS3 : S ≤ S ^ 3 := by nlinarith
    nlinarith
  have h_dom3 : Delta ^ 4 ≤ Delta * S ^ 3 := by
    have hD2 : Delta ^ 2 ≤ Delta := by nlinarith
    have hD2_one : Delta ^ 2 ≤ 1 := by nlinarith
    have hD4 : Delta ^ 4 ≤ Delta := by
      calc
        Delta ^ 4 = Delta ^ 2 * Delta ^ 2 := by ring
        _ ≤ Delta ^ 2 * 1 := by gcongr
        _ ≤ Delta := by nlinarith [hD2]
    have hS3 : 1 ≤ S ^ 3 := by nlinarith
    nlinarith
  calc
    3 *
      (dSig *
          (210 * sigSum ^ 3 + 360 * |c| * sigSum ^ 2 +
            216 * c ^ 2 * sigSum + 111 * sigSum ^ 2 * dSig +
            36 * |c| * sigSum * dSig + 36 * c ^ 2 * dSig +
            30 * sigSum * dSig ^ 2 + 3 * dSig ^ 3)
        + (6 * dC) ^ 2 * (3 * sig2 ^ 2 - 2 * c * sig2 + c ^ 2)
        + (3 * dC ^ 2) ^ 2)
        ≤ 3 * (Delta * (786 * S ^ 3 + 183 * S ^ 2 * Delta + 30 * S * Delta ^ 2 + 3 * Delta ^ 3) +
            216 * Delta ^ 2 * S ^ 2 + 9 * Delta ^ 4) := by gcongr
    _ = 2358 * Delta * S ^ 3 + 1197 * Delta ^ 2 * S ^ 2 + 90 * Delta ^ 3 * S + 36 * Delta ^ 4 := by ring
    _ ≤ 3681 * Delta * S ^ 3 := by
      nlinarith [h_dom1, h_dom2, h_dom3]

/-- Specialization of `shell_upper_poly_le_of_bounds` to the actual standard UV
shell upper function. This exposes the current algebraic content of the shell
branch: once the covariance quantities are bounded by `S` and `Delta`, the shell
upper function is bounded by `3681 * Delta * S^3`. -/
private theorem wickPowerStandardSeqShellUpper_le_of_size_bounds
    (params : Phi4Params) (n : ℕ) (x : Spacetime2D)
    {S Delta : ℝ}
    (hS0 : 0 ≤ S) (hS1 : 1 ≤ S)
    (hDelta0 : 0 ≤ Delta) (hDelta1 : Delta ≤ 1)
    (hc :
      |regularizedPointCovariance params.mass (standardUVCutoffSeq n)| ≤ S)
    (hsigSum :
      GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
          (uvMollifier (standardUVCutoffSeq n) x) (uvMollifier (standardUVCutoffSeq n) x) +
        GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
          (uvMollifier (standardUVCutoffSeq (n + 1)) x)
          (uvMollifier (standardUVCutoffSeq (n + 1)) x) ≤ S)
    (hsig2 :
      GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
        (uvMollifier (standardUVCutoffSeq (n + 1)) x)
        (uvMollifier (standardUVCutoffSeq (n + 1)) x) ≤ S)
    (hdSig :
      GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
        (uvMollifier (standardUVCutoffSeq (n + 1)) x - uvMollifier (standardUVCutoffSeq n) x)
        (uvMollifier (standardUVCutoffSeq (n + 1)) x - uvMollifier (standardUVCutoffSeq n) x)
        ≤ Delta)
    (hdC :
      |regularizedPointCovariance params.mass (standardUVCutoffSeq (n + 1)) -
          regularizedPointCovariance params.mass (standardUVCutoffSeq n)| ≤ Delta) :
    wickPowerStandardSeqShellUpper params n x ≤ 3681 * Delta * S ^ 3 := by
  let κ₁ := standardUVCutoffSeq n
  let κ₂ := standardUVCutoffSeq (n + 1)
  let c := regularizedPointCovariance params.mass κ₁
  let σ₁ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₁ x) (uvMollifier κ₁ x)
  let σ₂ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₂ x) (uvMollifier κ₂ x)
  let δσ := GaussianField.covariance (freeCovarianceCLM params.mass params.mass_pos)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
    (uvMollifier κ₂ x - uvMollifier κ₁ x)
  let δc := regularizedPointCovariance params.mass κ₂ - regularizedPointCovariance params.mass κ₁
  have hσ₁0 : 0 ≤ σ₁ := by
    dsimp [σ₁, κ₁]
    exact covariance_self_nonneg params.mass params.mass_pos (uvMollifier (standardUVCutoffSeq n) x)
  have hσ₂0 : 0 ≤ σ₂ := by
    dsimp [σ₂, κ₂]
    exact covariance_self_nonneg params.mass params.mass_pos
      (uvMollifier (standardUVCutoffSeq (n + 1)) x)
  have hδσ0 : 0 ≤ δσ := by
    dsimp [δσ, κ₁, κ₂]
    exact covariance_self_nonneg params.mass params.mass_pos
      (uvMollifier (standardUVCutoffSeq (n + 1)) x - uvMollifier (standardUVCutoffSeq n) x)
  have hσsum0 : 0 ≤ σ₁ + σ₂ := add_nonneg hσ₁0 hσ₂0
  simpa [wickPowerStandardSeqShellUpper, κ₁, κ₂, c, σ₁, σ₂, δσ, δc] using
    shell_upper_poly_le_of_bounds
      (S := S) (Delta := Delta) (c := c) (sigSum := σ₁ + σ₂) (sig2 := σ₂)
      (dSig := δσ) (dC := δc)
      hS0 hS1 hDelta0 hDelta1 hσsum0 hσ₂0 hδσ0
      hc hsigSum hsig2 hdSig hdC


/-- Pointwise specialization of `wickPower_four_step_sq_expectation_le_covariance`
to the canonical UV shell `standardUVCutoffSeq n -> standardUVCutoffSeq (n+1)`. -/
private theorem wickPower_standardSeq_step_sq_expectation_le_shellUpper
    (params : Phi4Params) (n : ℕ) (x : Spacetime2D) :
    ∫ ω : FieldConfig2D,
      (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
        wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
      ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ wickPowerStandardSeqShellUpper params n x := by
  simpa [wickPowerStandardSeqShellUpper] using
    wickPower_four_step_sq_expectation_le_covariance
      params.mass params.mass_pos
      (standardUVCutoffSeq n) (standardUVCutoffSeq (n + 1)) x

/-- Honest frontier for the discrete shell branch in its reduced form: after the
algebraic and Gaussian-moment reductions above, the remaining mathematics is to
show that the spatial integral of `wickPowerStandardSeqShellUpper` decays at the
target rate.

For the current CLM-based Gaussian measure, this requires either a direct
covariance estimate for the harmonic-oscillator CLM covariance or a separate
flat-space CLM realization as in `gap_covariance_eq_kernel`, followed by a
comparison/identification step. The local Wick algebra is no longer the
blocker. -/
theorem gap_wickPowerStandardSeqShellUpper_spatial_sq_rate
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet, wickPowerStandardSeqShellUpper params n x
        ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
  sorry

/-- Derived discrete shell-rate theorem for the actual quartic Wick-power step.

The remaining open mathematics has been pushed down to
`gap_wickPowerStandardSeqShellUpper_spatial_sq_rate`, which controls the
explicit shell-upper quantity extracted from the A/B/C decomposition. This
theorem bridges back to the original quartic-step statement used downstream. -/
theorem gap_wickPower_standardSeq_spatial_sq_rate
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
  obtain ⟨D, hD, h_shellUpper⟩ := gap_wickPowerStandardSeqShellUpper_spatial_sq_rate params Λ
  refine ⟨D, hD, ?_⟩
  intro n
  have hpoint :
      (fun x : Spacetime2D =>
        ∫ ω : FieldConfig2D,
          (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
            wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos))
        ≤ᵐ[MeasureTheory.volume.restrict Λ.toSet]
          fun x => wickPowerStandardSeqShellUpper params n x := by
    exact Filter.Eventually.of_forall
      (fun x => wickPower_standardSeq_step_sq_expectation_le_shellUpper params n x)
  have hstep_int :
      params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
        ≤
      params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet, wickPowerStandardSeqShellUpper params n x := by
    have h_rhs_int :
        Integrable (fun x => wickPowerStandardSeqShellUpper params n x)
          (MeasureTheory.volume.restrict Λ.toSet) :=
      integrable_wickPowerStandardSeqShellUpper params n Λ
    have h_nonneg :
        0 ≤ᵐ[MeasureTheory.volume.restrict Λ.toSet]
          fun x =>
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos) := by
      exact Filter.Eventually.of_forall (fun x =>
        integral_nonneg (fun ω => sq_nonneg _))
    have h_nonneg_factor :
        0 ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal := by
      positivity
    have h_int_mono :
        ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
          ≤
        ∫ x in Λ.toSet, wickPowerStandardSeqShellUpper params n x := by
      exact integral_mono_of_nonneg h_nonneg h_rhs_int hpoint
    exact mul_le_mul_of_nonneg_left h_int_mono h_nonneg_factor
  exact le_trans hstep_int (h_shellUpper n)

/-- The L² increment rate for the cutoff interaction along the canonical UV
    cutoff sequence.

    This theorem is now reduced to the explicit discrete shell estimate
    `gap_wickPower_standardSeq_spatial_sq_rate`. For the current CLM-based
    Gaussian measure, the remaining missing mathematics is a covariance-shell
    decay bound for the spatially integrated quartic Wick-power step.

    If the flat-space CLM existence frontier `gap_covariance_eq_kernel` is
    resolved and connected back to the current Gaussian layer, the expected
    flat-space heuristic is that the covariance increment on the shell
    `κ_n -> κ_{n+1}` gains the rate `log(n+2) / (n+1)^(3/2)`. -/
theorem gap_interactionCutoff_standardSeq_L2_increment_rate
    (params : Phi4Params) (Λ : Rectangle) :
    ∃ D : ℝ, 0 < D ∧ ∀ n : ℕ,
      ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
  let μ := freeFieldMeasure params.mass params.mass_pos
  have h_reduction :
      ∀ n : ℕ,
        ∫ ω : FieldConfig2D,
            (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
              interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ
          ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
              ∫ x in Λ.toSet,
                ∫ ω : FieldConfig2D,
                  (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                    wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2 ∂μ := by
    intro n
    simpa [μ] using
      interactionCutoff_sub_sq_le_spatialIntegral params Λ
        (standardUVCutoffSeq n) (standardUVCutoffSeq (n + 1))
  obtain ⟨D, hD, h_shell⟩ := gap_wickPower_standardSeq_spatial_sq_rate params Λ
  refine ⟨D, hD, ?_⟩
  intro n
  calc
    ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
          interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ
      ≤ params.coupling ^ 2 * (MeasureTheory.volume Λ.toSet).toReal *
          ∫ x in Λ.toSet,
            ∫ ω : FieldConfig2D,
              (wickPower 4 params.mass (standardUVCutoffSeq (n + 1)) ω x -
                wickPower 4 params.mass (standardUVCutoffSeq n) ω x) ^ 2 ∂μ := h_reduction n
    _ ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := h_shell n

/-- The model upper bound `sqrt(D² log²(n+2) / (n+1)^3)` is summable. -/
private theorem summable_sqrt_log_sq_div_cube (D : ℝ) (hD : 0 < D) :
    Summable (fun n : ℕ =>
      Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3)) := by
  have h_rpow_summable : Summable (fun n : ℕ => ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) := by
    have h_key : (fun n : ℕ => ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) =
        (fun n : ℕ => ((n : ℝ) ^ (-((5 : ℝ) / 4)))) ∘ Nat.succ := by
      ext n
      simp [Nat.cast_succ]
    rw [h_key]
    refine Summable.comp_injective ?_ Nat.succ_injective
    convert Real.summable_nat_rpow_inv.mpr (by norm_num : (1 : ℝ) < 5 / 4) using 1
    ext n
    rw [Real.rpow_neg (Nat.cast_nonneg n)]
  have h_upper_summable : Summable (fun n : ℕ =>
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) :=
    h_rpow_summable.mul_left (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D)
  refine Summable.of_nonneg_of_le (fun n => Real.sqrt_nonneg _) ?_ h_upper_summable
  intro n
  have hn1 : 0 < (n : ℝ) + 1 := by positivity
  have hn2 : 0 < (n : ℝ) + 2 := by positivity
  have hlog1 : Real.log ((n : ℝ) + 2) ≤ 4 * ((n : ℝ) + 2) ^ ((1 : ℝ) / 4) := by
    have hlog := Real.log_le_rpow_div hn2.le (by norm_num : (0 : ℝ) < 1 / 4)
    linarith
  have hlog2 : ((n : ℝ) + 2) ^ ((1 : ℝ) / 4) ≤
      (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    rw [← Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (le_of_lt hn1)]
    exact Real.rpow_le_rpow hn2.le (by linarith) (by norm_num)
  have hlog3 : Real.log ((n : ℝ) + 2) ≤
      4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    linarith [mul_le_mul_of_nonneg_left hlog2 (by norm_num : (0 : ℝ) ≤ 4)]
  have hlog_nonneg : 0 ≤ Real.log ((n : ℝ) + 2) := by
    exact Real.log_nonneg (by linarith)
  have hlog3_nonneg : 0 ≤ 4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4) := by
    positivity
  have hlog4 : Real.log ((n : ℝ) + 2) ^ 2 ≤
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 :=
    by nlinarith
  have hlog5 : (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * ((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 =
      16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    have h_two : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
      rw [Real.sqrt_eq_rpow, sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      norm_num
    have h_one : (((n : ℝ) + 1) ^ ((1 : ℝ) / 4)) ^ 2 = ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
      rw [sq, ← Real.rpow_add hn1]
      norm_num
    rw [mul_pow, mul_pow, h_two, h_one]
    norm_num
  have hlog_sq_bound : Real.log ((n : ℝ) + 2) ^ 2 ≤
      16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) := by
    exact hlog4.trans_eq hlog5
  have htarget_nonneg : 0 ≤
      (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ)) := by
    positivity
  have hsq : D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3 ≤
      ((4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
    have h_div : ((n : ℝ) + 1) ^ ((1 : ℝ) / 2) / ((n : ℝ) + 1) ^ 3 =
        ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [← Real.rpow_sub_natCast' hn1.le (by norm_num : (1 : ℝ) / 2 - 3 ≠ 0)]
      norm_num
    have h_const_sq : (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) ^ 2 =
        16 * Real.sqrt 2 * D ^ 2 := by
      rw [mul_pow, mul_pow]
      have h_two : ((2 : ℝ) ^ ((1 : ℝ) / 4)) ^ 2 = Real.sqrt 2 := by
        rw [Real.sqrt_eq_rpow, sq, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
        norm_num
      rw [h_two]
      ring
    have h_rpow_sq : (((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 =
        ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
      rw [sq, ← Real.rpow_add hn1]
      norm_num
    calc
      D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3
          ≤ D ^ 2 * (16 * Real.sqrt 2 * ((n : ℝ) + 1) ^ ((1 : ℝ) / 2)) / (↑n + 1) ^ 3 := by
              exact div_le_div_of_nonneg_right
                (mul_le_mul_of_nonneg_left hlog_sq_bound (by positivity))
                (by positivity)
      _ = D ^ 2 * (16 * Real.sqrt 2) * (((n : ℝ) + 1) ^ ((1 : ℝ) / 2) / ((n : ℝ) + 1) ^ 3) := by
            ring
      _ = D ^ 2 * (16 * Real.sqrt 2) * ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
            rw [h_div]
      _ = (16 * Real.sqrt 2 * D ^ 2) * ((n : ℝ) + 1) ^ (-(5 / 2 : ℝ)) := by
            ring
      _ = (4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) ^ 2 * (((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
            rw [h_const_sq, h_rpow_sq]
      _ = ((4 * (2 : ℝ) ^ ((1 : ℝ) / 4) * D) * ((n : ℝ) + 1) ^ (-(5 / 4 : ℝ))) ^ 2 := by
            ring_nf
  exact (Real.sqrt_le_iff).2 ⟨htarget_nonneg, hsq⟩

/-- The L¹ increments of the cutoff interaction along the canonical UV cutoff
    sequence are summable: Σ_n E[|V_{κ_{n+1}} - V_{κ_n}|] < ∞.

    This is the key analytical estimate for a.e. convergence. It follows from
    the L² increment rate bound (`gap_interactionCutoff_standardSeq_L2_increment_rate`)
    via Cauchy-Schwarz: E[|X|] ≤ ‖X‖₂ under a probability measure.

    Reference: Simon, "P(φ)₂", Chapter II (Theorem II.11). -/
theorem gap_interactionCutoff_standardSeq_summable_L1_increments
    (params : Phi4Params) (Λ : Rectangle) :
    Summable (fun n : ℕ =>
      ∫ ω : FieldConfig2D,
        |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω|
        ∂(freeFieldMeasure params.mass params.mass_pos)) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  -- Get the L² rate bound
  obtain ⟨D, hD, h_L2_rate⟩ :=
    gap_interactionCutoff_standardSeq_L2_increment_rate params Λ
  -- Each cutoff is L², hence differences are integrable
  have hf_int : ∀ n, Integrable
      (fun ω => interactionCutoff params Λ (standardUVCutoffSeq n) ω) μ :=
    fun n => (interactionCutoff_memLp_two params Λ
      (standardUVCutoffSeq n)).integrable one_le_two
  have hdiff_int : ∀ n, Integrable (fun ω =>
      interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
      interactionCutoff params Λ (standardUVCutoffSeq n) ω) μ :=
    fun n => (hf_int (n + 1)).sub (hf_int n)
  -- Each L¹ increment ≤ √(L² rate bound)
  have hdiff_sq_int : ∀ n, Integrable (fun ω =>
      (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
       interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2) μ :=
    fun n => ((interactionCutoff_memLp_two params Λ
      (standardUVCutoffSeq (n + 1))).sub
      (interactionCutoff_memLp_two params Λ
        (standardUVCutoffSeq n))).integrable_norm_rpow
      (by simp) (by simp) |>.congr
      (by filter_upwards with ω
          simp [Real.norm_eq_abs, ENNReal.toReal_ofNat])
  have h_bound : ∀ n, ∫ ω,
      |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
       interactionCutoff params Λ (standardUVCutoffSeq n) ω| ∂μ ≤
      Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3) := by
    intro n
    calc ∫ ω, |interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
           interactionCutoff params Λ (standardUVCutoffSeq n) ω| ∂μ
        ≤ Real.sqrt (∫ ω, (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2 ∂μ) :=
          integral_abs_le_sqrt_integral_sq (hdiff_int n) (hdiff_sq_int n)
      _ ≤ Real.sqrt (D ^ 2 * (Real.log (↑n + 2)) ^ 2 / (↑n + 1) ^ 3) :=
          Real.sqrt_le_sqrt (h_L2_rate n)
  -- The bound sequence is summable
  refine Summable.of_nonneg_of_le
    (fun n => integral_nonneg (fun ω => abs_nonneg _)) h_bound ?_
  -- Σ √(D²·log²(n+2)/(n+1)³) = Σ D·log(n+2)/(n+1)^{3/2} is summable
  exact summable_sqrt_log_sq_div_cube D hD

/-- Sequence-level a.e. convergence: V_{κ_n} → V a.e. along the canonical cutoff
    sequence `standardUVCutoffSeq n = ⟨n+1, ...⟩`.

    This is the natural first target: the Fatou bridge only needs discrete
    convergence, and `interaction` is defined as `Filter.limsup` of the sequence,
    so convergence holds whenever the limsup equals the limit.

    Strategy: From the summability of L¹ increments
    (`gap_interactionCutoff_standardSeq_summable_L1_increments`), we get
    E[Σ_n |V_{n+1} - V_n|] < ∞ by Tonelli/MCT, hence Σ_n |V_{n+1} - V_n| < ∞
    a.e. This gives absolute convergence of the telescoping series, so V_n
    converges a.e. The limit equals `interaction` (= limsup) by
    `Filter.Tendsto.limsup_eq`. -/
theorem gap_interactionCutoff_standardSeq_ae_convergence
    (params : Phi4Params) (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  set μ := freeFieldMeasure params.mass params.mass_pos
  set f : ℕ → FieldConfig2D → ℝ := fun n ω =>
    interactionCutoff params Λ (standardUVCutoffSeq n) ω
  have h_summable := gap_interactionCutoff_standardSeq_summable_L1_increments params Λ
  -- Step 1: from summable L¹ increments, derive a.e. pointwise absolute summability
  -- by MCT/Tonelli: E[∑|Δ_n|] = ∑E[|Δ_n|] < ∞ ⟹ ∑|Δ_n(ω)| < ∞ a.e.
  have hf_meas : ∀ n, Measurable (f n) := fun n =>
    (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq n)).measurable
  have h_ae_abs_summable : ∀ᵐ ω ∂μ,
      Summable (fun n => |f (n + 1) ω - f n ω|) := by
    -- Use lintegral_tsum + ae_lt_top
    have hdiff_meas : ∀ n, Measurable (fun ω => (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞)) :=
      fun n => ((hf_meas (n + 1)).sub (hf_meas n)).nnnorm.coe_nnreal_ennreal
    have h_lintegral_eq : ∫⁻ ω, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ =
        ∑' n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ :=
      lintegral_tsum (fun n => (hdiff_meas n).aemeasurable)
    -- Each f_n is L², hence integrable; differences are integrable
    have hf_integrable : ∀ n, Integrable (f n) μ :=
      fun n => (interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n)).integrable one_le_two
    have hdiff_integrable : ∀ n, Integrable (fun ω => f (n + 1) ω - f n ω) μ :=
      fun n => (hf_integrable (n + 1)).sub (hf_integrable n)
    have h_tsum_ne_top : ∑' n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ ≠ ⊤ := by
      -- Convert each lintegral to ENNReal.ofReal (∫ ‖Δ_n‖ dμ) via lintegral_coe_eq_integral
      have h_eq : ∀ n, ∫⁻ ω, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ =
          ENNReal.ofReal (∫ ω, ‖f (n + 1) ω - f n ω‖ ∂μ) :=
        fun n => lintegral_coe_eq_integral _ ((hdiff_integrable n).norm)
      simp_rw [h_eq]
      -- ∑' n, ENNReal.ofReal (∫ ‖Δ_n‖ dμ) ≠ ⊤
      have h_nn : ∀ n, 0 ≤ ∫ ω, ‖f (n + 1) ω - f n ω‖ ∂μ :=
        fun n => integral_nonneg (fun ω => norm_nonneg _)
      simp_rw [ENNReal.ofReal_eq_coe_nnreal (h_nn _)]
      rw [ENNReal.tsum_coe_ne_top_iff_summable]
      refine NNReal.summable_coe.1 ?_
      simp only [NNReal.coe_mk]
      simp_rw [Real.norm_eq_abs]
      exact h_summable
    have h_lintegral_ne_top : ∫⁻ ω, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ∂μ ≠ ⊤ :=
      h_lintegral_eq ▸ h_tsum_ne_top
    have h_ae_lt_top : ∀ᵐ ω ∂μ, ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) < ⊤ :=
      ae_lt_top (Measurable.ennreal_tsum hdiff_meas) h_lintegral_ne_top
    filter_upwards [h_ae_lt_top] with ω hω
    have hω' : ∑' n, (‖f (n + 1) ω - f n ω‖₊ : ℝ≥0∞) ≠ ⊤ := ne_of_lt hω
    rw [ENNReal.tsum_coe_ne_top_iff_summable] at hω'
    have h_nnnorm_summable := NNReal.summable_coe.2 hω'
    simp only [coe_nnnorm, Real.norm_eq_abs] at h_nnnorm_summable
    exact h_nnnorm_summable
  -- Step 2: for a.e. ω with absolutely summable differences, the sequence converges
  filter_upwards [h_ae_abs_summable] with ω h_abs_sum
  -- Cauchy from summable dist
  have h_summable_dist : Summable (fun n => dist (f n ω) (f n.succ ω)) := by
    refine h_abs_sum.congr (fun n => ?_)
    rw [Real.dist_eq, abs_sub_comm]
  have h_cauchy : CauchySeq (fun n => f n ω) :=
    cauchySeq_of_summable_dist h_summable_dist
  -- Complete → convergent
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete h_cauchy
  -- The limit equals the limsup (= interaction)
  have hL_eq : interaction params Λ ω = L := by
    unfold interaction
    exact hL.limsup_eq
  rw [hL_eq]
  exact hL

/-- L² convergence of the cutoff interaction to the limiting interaction. -/
theorem gap_interactionCutoff_L2_convergence (params : Phi4Params) (Λ : Rectangle) :
    Filter.Tendsto
      (fun (κ : ℝ) => if h : 0 < κ then
        ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
          ∂(freeFieldMeasure params.mass params.mass_pos)
        else 0)
      Filter.atTop
      (nhds 0) := by
  sorry

/-- A.e. convergence of the cutoff interaction to the limiting interaction
    (continuous-parameter version). Stronger than sequence-level, not needed
    for the main WP1 endpoint. -/
theorem gap_interactionCutoff_ae_convergence (params : Phi4Params) (Λ : Rectangle) :
    ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
      Filter.Tendsto
        (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
        Filter.atTop
        (nhds (interaction params Λ ω)) := by
  sorry

/-- Measurability of the limiting interaction. -/
theorem gap_interaction_aestronglyMeasurable (params : Phi4Params) (Λ : Rectangle) :
    AEStronglyMeasurable (interaction params Λ)
      (freeFieldMeasure params.mass params.mass_pos) := by
  -- interaction = Filter.limsup of interactionCutoff (standardUVCutoffSeq n)
  -- Each cutoff is StronglyMeasurable → Measurable
  -- Measurable.limsup → interaction is Measurable → AEStronglyMeasurable
  unfold interaction
  apply Measurable.aestronglyMeasurable
  apply Measurable.limsup
  intro n
  exact (interactionCutoff_stronglyMeasurable params Λ (standardUVCutoffSeq n)).measurable

/-- If the successive `L²` norms of `f_{n+1} - f_n` are summable and `f_n → g`
    a.e., then `g ∈ L²`. This is the structural bridge needed for the discrete
    UV-cutoff route. -/
private theorem memLp_two_of_tendsto_ae_of_summable_lpNorm_sub
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : ℕ → α → ℝ} {g : α → ℝ}
    (hf : ∀ n, MemLp (f n) 2 μ)
    (h_lim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (nhds (g x)))
    {d : ℕ → ℝ} (hd_sum : Summable d)
    (h_step : ∀ n, lpNorm (fun x => f (n + 1) x - f n x) 2 μ ≤ d n) :
    MemLp g 2 μ := by
  let F : ℕ → α →₂[μ] ℝ := fun n => (hf n).toLp (f n)
  have hdist : ∀ n, dist (F n) (F (n + 1)) ≤ d n := by
    intro n
    rw [dist_comm, dist_eq_norm]
    have hsub_mem : MemLp (fun x => f (n + 1) x - f n x) 2 μ := (hf (n + 1)).sub (hf n)
    have hsub_eq_toLp : (Lp.memLp (F (n + 1) - F n)).toLp (fun x => (F (n + 1) - F n) x) =
        hsub_mem.toLp (fun x => f (n + 1) x - f n x) := by
      apply (MemLp.toLp_eq_toLp_iff (Lp.memLp (F (n + 1) - F n)) hsub_mem).2
      filter_upwards [Lp.coeFn_sub (F (n + 1)) (F n), (hf (n + 1)).coeFn_toLp,
        (hf n).coeFn_toLp] with x hx h1 h0
      calc
        (F (n + 1) - F n) x = F (n + 1) x - F n x := by simpa using hx
        _ = f (n + 1) x - f n x := by rw [h1, h0]
    have hsub_eq : F (n + 1) - F n = hsub_mem.toLp (fun x => f (n + 1) x - f n x) := by
      simpa using (Lp.toLp_coeFn (F (n + 1) - F n) (Lp.memLp (F (n + 1) - F n))).symm.trans
        hsub_eq_toLp
    rw [hsub_eq, Lp.norm_toLp, MeasureTheory.toReal_eLpNorm hsub_mem.aestronglyMeasurable]
    exact h_step n
  have h_cauchy : CauchySeq F :=
    cauchySeq_of_dist_le_of_summable d hdist hd_sum
  obtain ⟨G, hG⟩ := cauchySeq_tendsto_of_complete h_cauchy
  have h_meas_in_measure : TendstoInMeasure μ (fun n => F n) atTop G :=
    tendstoInMeasure_of_tendsto_Lp hG
  have hFn_in_measure : TendstoInMeasure μ f atTop G := by
    exact h_meas_in_measure.congr_left (fun n => (hf n).coeFn_toLp)
  have hg_in_measure : TendstoInMeasure μ f atTop g :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hf n).aestronglyMeasurable) h_lim
  have h_ae : (G : α → ℝ) =ᵐ[μ] g := tendstoInMeasure_ae_unique hFn_in_measure hg_in_measure
  exact MemLp.ae_eq h_ae (Lp.memLp G)

/-- Convert the shellwise `L²` increment rate into a bound on the real-valued
    `lpNorm` of the successive cutoff differences. -/
private theorem interactionCutoff_standardSeq_lpNorm_sub_le
    (params : Phi4Params) (Λ : Rectangle) {D : ℝ}
    (h_rate : ∀ n : ℕ,
      ∫ ω : FieldConfig2D,
        (interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
         interactionCutoff params Λ (standardUVCutoffSeq n) ω) ^ 2
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3) :
    ∀ n : ℕ,
      lpNorm
        (fun ω : FieldConfig2D =>
          interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
          interactionCutoff params Λ (standardUVCutoffSeq n) ω)
        2 (freeFieldMeasure params.mass params.mass_pos)
      ≤ Real.sqrt (D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3) := by
  intro n
  have hdiff_mem : MemLp
      (fun ω : FieldConfig2D =>
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
        interactionCutoff params Λ (standardUVCutoffSeq n) ω)
      2 (freeFieldMeasure params.mass params.mass_pos) :=
    ((interactionCutoff_memLp_two params Λ (standardUVCutoffSeq (n + 1))).sub
      (interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n)))
  rw [lpNorm_eq_integral_norm_rpow_toReal two_ne_zero ENNReal.ofNat_ne_top
    hdiff_mem.aestronglyMeasurable]
  have h_sq :
      ∫ ω : FieldConfig2D,
          ‖interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω‖ ^ (2 : ℝ)
        ∂(freeFieldMeasure params.mass params.mass_pos)
      ≤ D ^ 2 * (Real.log (n + 2)) ^ 2 / (n + 1) ^ 3 := by
    simpa [sq_abs] using h_rate n
  have h_nonneg : 0 ≤
      ∫ ω : FieldConfig2D,
          ‖interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω -
            interactionCutoff params Λ (standardUVCutoffSeq n) ω‖ ^ (2 : ℝ)
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
    exact integral_nonneg (fun _ => by positivity)
  have := Real.rpow_le_rpow h_nonneg h_sq (by norm_num : 0 ≤ (1 / 2 : ℝ))
  simpa [Real.sqrt_eq_rpow, one_div] using this

/-- Square integrability of the limiting interaction.
    Strategy: from L² convergence (Vκ → V in L²), the limit V ∈ L² by completeness.
    Concretely: V² ≤ 2(V - Vκ)² + 2Vκ² pointwise, so ∫V² ≤ 2∫(V-Vκ)² + 2∫Vκ² < ∞. -/
theorem gap_interaction_sq_integrable (params : Phi4Params) (Λ : Rectangle) :
    Integrable (fun ω => (interaction params Λ ω) ^ 2)
      (freeFieldMeasure params.mass params.mass_pos) := by
  obtain ⟨D, hD, h_rate⟩ := gap_interactionCutoff_standardSeq_L2_increment_rate params Λ
  have h_mem : MemLp (interaction params Λ) 2 (freeFieldMeasure params.mass params.mass_pos) := by
    apply memLp_two_of_tendsto_ae_of_summable_lpNorm_sub
      (hf := fun n => interactionCutoff_memLp_two params Λ (standardUVCutoffSeq n))
      (h_lim := gap_interactionCutoff_standardSeq_ae_convergence params Λ)
      (hd_sum := summable_sqrt_log_sq_div_cube D hD)
    intro n
    exact interactionCutoff_standardSeq_lpNorm_sub_le params Λ h_rate n
  exact (memLp_two_iff_integrable_sq (gap_interaction_aestronglyMeasurable params Λ)).1 h_mem
