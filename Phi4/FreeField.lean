/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Defs
import Phi4.Bessel.BesselK0
import HeatKernel
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.BumpFunction.Normed

/-!
# Free Euclidean Field in 2D

The free Euclidean field is a centered Gaussian measure on S'(ℝ²). The Gaussian
measure is constructed using `GaussianField.measure` from the gaussian-field
library, which works for any continuous linear map T : E →L[ℝ] H. The covariance
is C(f,g) = ⟨T(f), T(g)⟩_H.

**Important**: The CLM `freeCovarianceCLM` is diagonal in the Hermite basis
(via `spectralCLM`) with eigenvalues (2n₁+1) + (2n₂+1) + m². This gives the
covariance of the **harmonic oscillator resolvent** (-Δ + |x|² + m²)⁻¹, NOT
the flat-space resolvent (-Δ + m²)⁻¹. The flat-space Green's function is defined
separately as `freeCovKernel` and is used for position-space kernel estimates.
See `covariance_spectral_sum` and ProofIdeas/CovarianceMismatch.md.

## Main definitions

* `freeEigenvalue` — Eigenvalues λₘ of (-Δ + |x|² + m²) in the Hermite basis
* `freeSingularValue` — Singular values σₘ = λₘ⁻¹/² of the covariance
* `freeCovarianceCLM` — The CLM T : S(ℝ²) →L[ℝ] ℓ² (harmonic oscillator covariance)
* `freeFieldMeasure` — The Gaussian probability measure dφ_C on S'(ℝ²)
* `freeCovKernel` — Flat-space Green's function (-Δ + m²)⁻¹

## References

* [Glimm-Jaffe] Sections 6.2, 7.1-7.2
* gaussian-field library: `GaussianField.measure`, `GaussianField.Properties`
-/

noncomputable section

open MeasureTheory GaussianField
open scoped NNReal

/-! ## Eigenvalue spectrum of (-Δ + x² + m²) on ℝ²

The Hermite functions provide an eigenbasis for the harmonic oscillator H = -Δ + x²
on ℝ. The operator H + m² has discrete spectrum and compact resolvent.
For ℝ², in the tensor Hermite basis ψ_{n₁} ⊗ ψ_{n₂}, the eigenvalues of
(H₁ + H₂ + m²) = (-∂₁² + x₁² - ∂₂² + x₂² + m²) are
(2n₁ + 1) + (2n₂ + 1) + m².

Note: These are eigenvalues of the harmonic oscillator (-Δ + x² + m²), NOT of
the flat-space operator (-Δ + m²). The latter has continuous spectrum [m², ∞).
We use the harmonic oscillator basis because it gives a nuclear embedding
S(ℝ²) ↪ L²(ℝ²) via the Dynin-Mityagin theorem, which is required for the
Gaussian measure construction. Since `spectralCLM` is diagonal in this basis,
`freeCovarianceCLM` gives the harmonic oscillator covariance (-Δ+|x|²+m²)⁻¹. -/

/-- Eigenvalue of the harmonic oscillator (-Δ + x² + m²) for the m-th
    Hermite basis function (Cantor-paired index).
    λₘ = (2n₁ + 1) + (2n₂ + 1) + mass², where (n₁, n₂) = unpair(m).

    These are NOT eigenvalues of (-Δ + m²); they index the Hermite eigenbasis
    used for the nuclear embedding S(ℝ²) ↪ L²(ℝ²). -/
def freeEigenvalue (mass : ℝ) (m : ℕ) : ℝ :=
  let nk := m.unpair
  (2 * nk.1 + 1 : ℝ) + (2 * nk.2 + 1 : ℝ) + mass ^ 2

/-- The eigenvalues are positive for positive mass. -/
theorem freeEigenvalue_pos (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 < freeEigenvalue mass m := by
  unfold freeEigenvalue
  positivity

/-- Singular value σₘ = λₘ⁻¹/² of the free covariance.
    These are the diagonal entries of T in the adapted basis.
    Convention matches GaussianField.qftSingularValue: λ ^ (-1/2). -/
def freeSingularValue (mass : ℝ) (m : ℕ) : ℝ :=
  (freeEigenvalue mass m)⁻¹ ^ ((1 : ℝ)/2)

/-- The eigenvalues have a uniform lower bound: λₘ ≥ 2 + mass². -/
theorem freeEigenvalue_lower_bound (mass : ℝ) (m : ℕ) :
    2 + mass ^ 2 ≤ freeEigenvalue mass m := by
  unfold freeEigenvalue
  have h1 : (0 : ℝ) ≤ (m.unpair.1 : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) ≤ (m.unpair.2 : ℝ) := Nat.cast_nonneg _
  linarith

/-- The singular values are nonneg. -/
theorem freeSingularValue_nonneg (mass : ℝ) (hmass : 0 < mass) (m : ℕ) :
    0 ≤ freeSingularValue mass m :=
  Real.rpow_nonneg (inv_nonneg.mpr (le_of_lt (freeEigenvalue_pos mass hmass m))) _

/-- The singular values are bounded (needed for spectralCLM).
    Since λₘ ≥ 2 + mass² > 0, we have σₘ = λₘ⁻¹/² ≤ (2+mass²)⁻¹/². -/
theorem free_singular_values_bounded (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, ∀ m : ℕ, |freeSingularValue mass m| ≤ C := by
  use (2 + mass ^ 2)⁻¹ ^ ((1 : ℝ)/2)
  intro m
  rw [abs_of_nonneg (freeSingularValue_nonneg mass hmass m)]
  unfold freeSingularValue
  have hev_pos := freeEigenvalue_pos mass hmass m
  apply Real.rpow_le_rpow (inv_nonneg.mpr hev_pos.le)
  · exact (inv_le_inv₀ hev_pos (by positivity)).mpr (freeEigenvalue_lower_bound mass m)
  · positivity

/-- The singular values form a bounded sequence (IsBoundedSeq form for spectralCLM). -/
theorem free_singular_values_isBoundedSeq (mass : ℝ) (hmass : 0 < mass) :
    GaussianField.IsBoundedSeq (fun m => freeSingularValue mass m) :=
  free_singular_values_bounded mass hmass

/-! ## Free covariance CLM and Gaussian measure -/

/-- The covariance CLM T : S(ℝ²) →L[ℝ] ℓ² for the free field.
    This maps test functions to sequences via the Hermite expansion,
    weighted by the singular values σₘ:
      T(f)ₘ = σₘ · coeffₘ(f)
    where coeffₘ are the Schauder coefficients from the DyninMityagin basis. -/
def freeCovarianceCLM (mass : ℝ) (hmass : 0 < mass) :
    TestFun2D →L[ℝ] GaussianField.ell2' :=
  GaussianField.spectralCLM
    (fun m => freeSingularValue mass m)
    (free_singular_values_isBoundedSeq mass hmass)

/-- The free Gaussian field measure dφ_C on S'(ℝ²).
    This is the centered Gaussian probability measure with covariance
    C(f,g) = ⟨T(f), T(g)⟩_{ℓ²} = Σₘ σₘ² ĉₘ(f) ĉₘ(g)
    where ĉₘ are the Hermite coefficients. -/
def freeFieldMeasure (mass : ℝ) (hmass : 0 < mass) :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration :=
  GaussianField.measure (freeCovarianceCLM mass hmass)

/-! ## Properties of the free field measure

These follow directly from `GaussianField.Properties`. -/

/-- The free field measure is a probability measure. -/
theorem freeFieldMeasure_isProbability (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (freeFieldMeasure mass hmass) :=
  GaussianField.measure_isProbability _

/-- Cross-moment formula: E[ω(f)ω(g)] = covariance T f g. -/
theorem freeField_cross_moment (mass : ℝ) (hmass : 0 < mass)
    (f g : TestFun2D) :
    ∫ ω, ω f * ω g ∂(freeFieldMeasure mass hmass) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f g :=
  GaussianField.cross_moment_eq_covariance _ f g

/-- Exponential moments of linear pairings under the free field measure. -/
theorem freeField_pairing_exp_integrable (mass : ℝ) (hmass : 0 < mass)
    (f : TestFun2D) (t : ℝ) :
    Integrable (fun ω : FieldConfig2D => Real.exp (t * ω f))
      (freeFieldMeasure mass hmass) := by
  let T := freeCovarianceCLM mass hmass
  have hgauss := GaussianField.pairing_is_gaussian T f
  have hgaussInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        (ProbabilityTheory.gaussianReal 0
          ((@inner ℝ GaussianField.ell2' _ (T f) (T f) : ℝ).toNNReal)) :=
    ProbabilityTheory.integrable_exp_mul_gaussianReal (μ := 0)
      (v := ((@inner ℝ GaussianField.ell2' _ (T f) (T f) : ℝ).toNNReal)) t
  have hmapInt :
      Integrable (fun x : ℝ => Real.exp (t * x))
        ((freeFieldMeasure mass hmass).map (fun ω : FieldConfig2D => ω f)) := by
    simpa [freeFieldMeasure, T] using (hgauss.symm ▸ hgaussInt)
  simpa [Function.comp] using
    hmapInt.comp_measurable (GaussianField.configuration_eval_measurable f)

/-! ## Spectral decomposition of the free covariance

The covariance defined by `freeCovarianceCLM` decomposes as a sum over the
Hermite basis, since the CLM is diagonal:
  C(f,g) = Σₘ σₘ² · ĉₘ(f) · ĉₘ(g)
where σₘ = freeSingularValue, ĉₘ = DyninMityaginSpace.coeff.

**Important**: This is the covariance of the harmonic oscillator resolvent
(-Δ + |x|² + m²)⁻¹, NOT the flat-space resolvent (-Δ + m²)⁻¹. The two
operators differ because the Hermite basis diagonalizes the harmonic
oscillator but not the flat Laplacian. See ProofIdeas/CovarianceMismatch.md.
-/

/-- The Hilbert-space covariance equals the spectral sum:
    C(f,g) = Σₘ σₘ² · ĉₘ(f) · ĉₘ(g)
    where σₘ = (freeSingularValue mass m) and ĉₘ = DyninMityaginSpace.coeff m.

    This decomposes the covariance in the Hermite eigenbasis. -/
theorem covariance_spectral_sum (mass : ℝ) (hmass : 0 < mass)
    (f g : TestFun2D) :
    GaussianField.covariance (freeCovarianceCLM mass hmass) f g =
      ∑' m, (freeSingularValue mass m) ^ 2 *
        DyninMityaginSpace.coeff m f * DyninMityaginSpace.coeff m g := by
  unfold GaussianField.covariance freeCovarianceCLM
  rw [GaussianField.ell2_inner_eq_tsum]
  congr 1; ext m
  simp only [GaussianField.spectralCLM_coord]
  simp only [RCLike.inner_apply, RCLike.conj_to_real]
  ring

/-! ## The flat-space Green's function

The flat-space Green's function G(x,y) = (-Δ + m²)⁻¹(x,y) has an explicit
integral kernel in d=2: (2π)⁻¹ K₀(m|x-y|).

**Note**: This kernel is for the flat-space operator (-Δ + m²)⁻¹, which is
DIFFERENT from the covariance of `freeCovarianceCLM` (the harmonic oscillator
resolvent (-Δ + |x|² + m²)⁻¹). The flat-space kernel is used for:
- Position-space Feynman rules (`graphIntegral`, `localizedGraphIntegral`)
- Covariance comparison estimates (C_D ≤ C ≤ C_N)
- Bessel function bounds

Key properties:
- G(x,y) ~ -(2π)⁻¹ ln|x-y| as |x-y| → 0 (logarithmic divergence in d=2)
- G(x,y) ~ const × |x-y|⁻¹/² e^{-m|x-y|} as |x-y| → ∞ (exponential decay)
-/

/-- The flat-space Green's function G(x,y) = (-Δ+m²)⁻¹(x,y) on ℝ².

    Defined via the heat kernel representation:
      G(x,y) = ∫₀^∞ (4πt)⁻¹ exp(-m²t - |x-y|²/(4t)) dt

    This integral converges for mass > 0 and equals (2π)⁻¹ K₀(m|x-y|).

    **Warning**: This is NOT the kernel of the covariance defined by
    `freeCovarianceCLM`, which is the harmonic oscillator resolvent.
    See `covariance_spectral_sum` for the correct spectral decomposition
    of the CLM-based covariance. -/
def freeCovKernel (mass : ℝ) (x y : Spacetime2D) : ℝ :=
  ∫ t in Set.Ioi (0 : ℝ),
    (4 * Real.pi * t)⁻¹ * Real.exp (-(mass ^ 2 * t + ‖x - y‖ ^ 2 / (4 * t)))

/-- Honest theorem-level frontier for the flat-space free covariance:
    there exists a Gaussian CLM whose covariance pairing is the flat-space
    Green's function kernel.

    This is the mathematically correct replacement for the false statement that
    the already-defined `freeCovarianceCLM` (harmonic oscillator resolvent)
    equals the flat-space kernel. The missing work is to build a CLM
    representation of `(-Δ + m²)⁻¹`, or equivalently to construct the flat
    Gaussian free field directly on Schwartz test functions.

    **Status**: This requires either
    1. a non-diagonal CLM realizing the flat covariance, or
    2. a separate construction followed by an isometric identification with `ℓ²`.

    See `ProofIdeas/CovarianceMismatch.md`. -/
theorem gap_covariance_eq_kernel (mass : ℝ) (hmass : 0 < mass) :
    ∃ T : TestFun2D →L[ℝ] ↥ell2',
      ∀ (f g : TestFun2D),
        GaussianField.covariance T f g =
          ∫ x, ∫ y, f x * freeCovKernel mass x y * g y := by
  sorry

/-- Rewrite the free covariance kernel using the 2D Schwinger integral identity. -/
theorem freeCovKernel_eq_besselK0
    (mass : ℝ) (hmass : 0 < mass) (x y : Spacetime2D)
    (hxy : 0 < ‖x - y‖) :
    freeCovKernel mass x y = (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) := by
  have hsch :
      ∫ t in Set.Ioi (0 : ℝ), (1 / t) * Real.exp (-mass ^ 2 * t - ‖x - y‖ ^ 2 / (4 * t))
        = 2 * besselK0 (mass * ‖x - y‖) :=
    schwingerIntegral2D_eq_besselK0 mass ‖x - y‖ hmass hxy
  unfold freeCovKernel
  calc
    ∫ t in Set.Ioi (0 : ℝ), (4 * Real.pi * t)⁻¹ *
        Real.exp (-(mass ^ 2 * t + ‖x - y‖ ^ 2 / (4 * t)))
        = (4 * Real.pi)⁻¹ *
            (∫ t in Set.Ioi (0 : ℝ), (1 / t) *
              Real.exp (-mass ^ 2 * t - ‖x - y‖ ^ 2 / (4 * t))) := by
          rw [← integral_const_mul]
          apply integral_congr_ae
          filter_upwards with t
          ring_nf
    _ = (4 * Real.pi)⁻¹ * (2 * besselK0 (mass * ‖x - y‖)) := by rw [hsch]
    _ = (2 * Real.pi)⁻¹ * besselK0 (mass * ‖x - y‖) := by ring

/-- Positivity of the free covariance as a smeared quadratic form.
    This is the mathematically sound positivity statement used by the Gaussian
    construction: for any finite family of test functions, the covariance matrix
    is positive semidefinite. -/
theorem freeCovKernel_pos_def (mass : ℝ) (hmass : 0 < mass) :
    ∀ (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℝ),
      0 ≤ ∑ i, ∑ j, c i * c j *
        GaussianField.covariance (freeCovarianceCLM mass hmass) (f i) (f j) := by
  intro n f c
  let T := freeCovarianceCLM mass hmass
  have h_expand :
      @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ j, c j • T (f j))
      = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
    calc
      @inner ℝ GaussianField.ell2' _ (∑ i, c i • T (f i)) (∑ j, c j • T (f j))
          = ∑ i, @inner ℝ GaussianField.ell2' _ (c i • T (f i)) (∑ j, c j • T (f j)) := by
              simpa using
                (sum_inner (s := Finset.univ)
                  (f := fun i : Fin n => c i • T (f i))
                  (x := ∑ j, c j • T (f j)))
      _ = ∑ i, ∑ j, @inner ℝ GaussianField.ell2' _ (c i • T (f i)) (c j • T (f j)) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            simpa using
              (inner_sum (s := Finset.univ)
                (f := fun j : Fin n => c j • T (f j))
                (x := c i • T (f i)))
      _ = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            refine Finset.sum_congr rfl ?_
            intro j _
            simp [GaussianField.covariance, real_inner_smul_left, real_inner_smul_right]
            ring
  have h_nonneg :
      0 ≤ @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ i, c i • T (f i)) :=
    real_inner_self_nonneg
  calc
    0 ≤ @inner ℝ GaussianField.ell2' _
        (∑ i, c i • T (f i)) (∑ i, c i • T (f i)) := h_nonneg
    _ = ∑ i, ∑ j, c i * c j * GaussianField.covariance T (f i) (f j) := by
      simpa using h_expand

/-- UV mollifier: a smooth bump function centered at x with support of radius ~1/κ.
    This is the approximate delta function δ_{κ,x} used for UV regularization.
    The function is C^∞, compactly supported in a ball of radius κ⁻¹ around x,
    and is normalized to have total mass `1`.

    The exact choice of mollifier does not affect the UV limit (κ → ∞),
    only the intermediate regularized quantities. -/
def uvMollifier (κ : UVCutoff) (x : Spacetime2D) : TestFun2D :=
  let bump : ContDiffBump x :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  (bump.hasCompactSupport_normed (μ := MeasureTheory.volume)).toSchwartzMap
    (bump.contDiff_normed (μ := MeasureTheory.volume))

/-- The normalized UV mollifier has unit total mass. -/
theorem integral_uvMollifier (κ : UVCutoff) (x : Spacetime2D) :
    ∫ y, uvMollifier κ x y = 1 := by
  let bump : ContDiffBump x :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  have huv :
      (uvMollifier κ x : Spacetime2D → ℝ) = bump.normed MeasureTheory.volume := by
    ext y
    simp [uvMollifier, bump]
  rw [huv]
  exact bump.integral_normed (μ := MeasureTheory.volume)

/-- The support of the normalized UV mollifier is the outer bump ball. -/
theorem support_uvMollifier_eq (κ : UVCutoff) (x : Spacetime2D) :
    Function.support (uvMollifier κ x) = Metric.ball x κ.κ⁻¹ := by
  let bump : ContDiffBump x :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  have huv :
      (uvMollifier κ x : Spacetime2D → ℝ) = bump.normed MeasureTheory.volume := by
    ext y
    simp [uvMollifier, bump]
  rw [huv]
  simpa [bump] using (bump.support_normed_eq (μ := MeasureTheory.volume))

/-- The topological support of the normalized UV mollifier is the closed outer
support ball. -/
theorem tsupport_uvMollifier_eq (κ : UVCutoff) (x : Spacetime2D) :
    tsupport (uvMollifier κ x : Spacetime2D → ℝ) = Metric.closedBall x κ.κ⁻¹ := by
  rw [tsupport, support_uvMollifier_eq, closure_ball _ (inv_pos.mpr κ.hκ).ne']

/-- Pointwise size bound for the normalized UV mollifier. This is the natural
`κ²`-scale amplitude estimate for a unit-mass bump in two dimensions, expressed
in a coordinate-free volume form. -/
theorem uvMollifier_le_four_div_volume_closedBall
    (κ : UVCutoff) (x y : Spacetime2D) :
    uvMollifier κ x y ≤ 4 / MeasureTheory.volume.real (Metric.closedBall x κ.κ⁻¹) := by
  let bump : ContDiffBump x :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  have huv :
      (uvMollifier κ x : Spacetime2D → ℝ) = bump.normed MeasureTheory.volume := by
    ext z
    simp [uvMollifier, bump]
  rw [huv]
  have hrad : bump.rOut ≤ 2 * bump.rIn := by
    dsimp [bump]
    rw [inv_eq_one_div, inv_eq_one_div]
    field_simp [κ.hκ.ne']
    exact le_rfl
  calc
    bump.normed MeasureTheory.volume y
      ≤ 2 ^ 2 / MeasureTheory.volume.real (Metric.closedBall x κ.κ⁻¹) := by
        simpa [bump, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
          (bump.normed_le_div_measure_closedBall_rOut (μ := MeasureTheory.volume) 2 hrad y)
    _ = 4 / MeasureTheory.volume.real (Metric.closedBall x κ.κ⁻¹) := by norm_num

/-- Translation identity for the normalized UV mollifier. -/
theorem uvMollifier_apply_sub (κ : UVCutoff) (a y : Spacetime2D) :
    uvMollifier κ a y = uvMollifier κ 0 (y - a) := by
  let ba : ContDiffBump a :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  let b0 : ContDiffBump (0 : Spacetime2D) :=
    ⟨(2 * κ.κ)⁻¹, κ.κ⁻¹,
     inv_pos.mpr (mul_pos two_pos κ.hκ),
     by rw [inv_lt_inv₀ (mul_pos two_pos κ.hκ) κ.hκ]; linarith [κ.hκ]⟩
  have huvA : (uvMollifier κ a : Spacetime2D → ℝ) = ba.normed MeasureTheory.volume := by
    ext z
    simp [uvMollifier, ba]
  have huv0 : (uvMollifier κ (0 : Spacetime2D) : Spacetime2D → ℝ) = b0.normed MeasureTheory.volume := by
    ext z
    simp [uvMollifier, b0]
  have hraw : ∀ z : Spacetime2D, ba z = b0 (z - a) := by
    intro z
    rw [show ba z =
        (someContDiffBumpBase Spacetime2D).toFun (κ.κ⁻¹ / ((2 * κ.κ)⁻¹))
          (((2 * κ.κ)⁻¹)⁻¹ • (z - a)) by rfl]
    rw [show b0 (z - a) =
        (someContDiffBumpBase Spacetime2D).toFun (κ.κ⁻¹ / ((2 * κ.κ)⁻¹))
          (((2 * κ.κ)⁻¹)⁻¹ • ((z - a) - 0)) by rfl]
    simp [sub_eq_add_neg]
  have hint : ∫ z, ba z = ∫ z, b0 z := by
    calc
      ∫ z, ba z = ∫ z, b0 (z - a) := by
        refine integral_congr_ae ?_
        exact Filter.Eventually.of_forall hraw
      _ = ∫ z, b0 z := by
        simpa using
          (integral_sub_right_eq_self (f := fun z : Spacetime2D => b0 z) a
            (μ := MeasureTheory.volume))
  rw [huvA, huv0, ContDiffBump.normed_def, ContDiffBump.normed_def, hraw y, hint]

/-- The UV-regularized covariance c_κ = Cov(δ_{κ,0}, δ_{κ,0}), where δ_{κ,0} is
    the UV mollifier centered at the origin.
    This is the variance of the regularized field: c_κ = E[φ_κ(0)²].
    In d=2 one expects logarithmic UV growth; we only use the variance
    definition here. -/
def regularizedPointCovariance (mass : ℝ) (κ : UVCutoff) : ℝ :=
  if h : 0 < mass then
    GaussianField.covariance (freeCovarianceCLM mass h) (uvMollifier κ 0) (uvMollifier κ 0)
  else 0

/-- Honest mollifier-family covariance frontier.

This is the narrower identification actually used by the shell and Nelson
branches: the CLM covariance paired against UV mollifiers should match the
flat-space kernel smeared against the same mollifiers. It is strictly weaker
than `gap_covariance_eq_kernel`, but it exposes the real current blocker for
the UV analysis without requiring a full flat-space CLM construction. -/
theorem gap_uvMollifier_covariance_eq_freeCovKernel
    (mass : ℝ) (hmass : 0 < mass) :
    ∀ (κ₁ κ₂ : UVCutoff) (x y : Spacetime2D),
      GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ₁ x) (uvMollifier κ₂ y)
        =
      ∫ u, ∫ v, uvMollifier κ₁ x u * freeCovKernel mass u v * uvMollifier κ₂ y v := by
  sorry

/-- Kernel-side frontier for the logarithmic growth of the UV-regularized point
covariance.

Combined with `gap_covariance_eq_kernel`, this is the actual analytic leaf
behind `regularizedPointCovariance` growth: it isolates the mollifier-kernel
estimate from the separate CLM-to-kernel realization problem. -/
theorem gap_uvMollifier_freeCovKernel_log_growth (mass : ℝ) (hmass : 0 < mass) :
    ∃ K C₀ : ℝ, 0 < K ∧ 0 ≤ C₀ ∧
      ∀ κ : UVCutoff,
        (∫ x, ∫ y, uvMollifier κ 0 x * freeCovKernel mass x y * uvMollifier κ 0 y)
          ≤ C₀ + K * Real.log κ.κ := by
  sorry

end
