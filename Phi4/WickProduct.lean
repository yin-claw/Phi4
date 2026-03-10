/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.CovarianceOperators

/-!
# Wick Products (Normal Ordering)

Wick products :φ(x)ⁿ:_C are the renormalized powers of the field, defined by subtracting
the divergent self-contractions. They are characterized by:
  :φ(x)ⁿ:_C = Hₙ(φ(x), c_κ(x))
where Hₙ is the n-th Hermite polynomial and c_κ(x) = C_κ(x,x) is the regularized
pointwise covariance.

Explicitly for n=4 (the case we need):
  :φ⁴:_C = φ⁴ - 6c_κ φ² + 3c_κ²

The key properties are:
1. :φⁿ: ∈ Lp(dφ_C) for all p < ∞ (in d=2)
2. Re-Wick-ordering formula under change of covariance
3. Integration by parts for Wick products

## Main definitions

* `wickPower` — :φ(x)ⁿ:_C via Hermite polynomials
* `wickFourth` — :φ(x)⁴:_C = φ⁴ - 6cφ² + 3c²

## References

* [Glimm-Jaffe] Sections 6.3, 8.3, 8.6, 9.1
-/

noncomputable section

open MeasureTheory GaussianField ProbabilityTheory
open scoped ENNReal NNReal

/-! ## Wick products via Hermite polynomials -/

/-- The Wick monomial `:x^n:_c` (probabilists' Hermite polynomial scaled by variance c).

    Defined via the recursion:
      `:x⁰: = 1`, `:x¹: = x`, `:x^{n+2}: = x · :x^{n+1}: - (n+1)·c · :x^n:`

    This equals `c^{n/2} · Heₙ(x/√c)` where Heₙ is the probabilists' Hermite polynomial.
    The recursive definition avoids division by zero when c = 0 and is convenient
    for computation. Explicitly:
      He₀ = 1, He₁(x) = x, He₂(x,c) = x² - c,
      He₃(x,c) = x³ - 3cx, He₄(x,c) = x⁴ - 6cx² + 3c². -/
def wickMonomial : ℕ → ℝ → ℝ → ℝ
  | 0, _, _ => 1
  | 1, _, x => x
  | n + 2, c, x => x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x

@[simp]
theorem wickMonomial_zero (c x : ℝ) : wickMonomial 0 c x = 1 := rfl

@[simp]
theorem wickMonomial_one (c x : ℝ) : wickMonomial 1 c x = x := rfl

theorem wickMonomial_succ_succ (n : ℕ) (c x : ℝ) :
    wickMonomial (n + 2) c x =
    x * wickMonomial (n + 1) c x - (n + 1 : ℝ) * c * wickMonomial n c x := rfl

/-- Wick monomials at c = 0 are just ordinary monomials. -/
theorem wickMonomial_zero_variance : ∀ (n : ℕ) (x : ℝ),
    wickMonomial n 0 x = x ^ n
  | 0, x => by simp
  | 1, x => by simp
  | n + 2, x => by
    have h1 := wickMonomial_zero_variance (n + 1) x
    have h2 := wickMonomial_zero_variance n x
    simp only [wickMonomial_succ_succ, mul_zero, zero_mul, sub_zero, h1, h2]
    ring

/-- :x²:_c = x² - c -/
@[simp]
theorem wickMonomial_two (c x : ℝ) :
    wickMonomial 2 c x = x ^ 2 - c := by
  simp [wickMonomial_succ_succ]; ring

/-- :x⁴:_c = x⁴ - 6cx² + 3c² -/
@[simp]
theorem wickMonomial_four (c x : ℝ) :
    wickMonomial 4 c x = x ^ 4 - 6 * c * x ^ 2 + 3 * c ^ 2 := by
  simp [wickMonomial_succ_succ]; ring

/-- Legacy alias for backward compatibility -/
abbrev hermitePoly := wickMonomial

/-- The UV-regularized field φ_κ(x) = ⟨ω, δ_{κ,x}⟩ evaluated at a spacetime point.
    This is the raw (un-Wick-ordered) field value, obtained by applying the distributional
    field configuration ω ∈ S'(ℝ²) to the UV mollifier δ_{κ,x} ∈ S(ℝ²).
    The mollifier δ_{κ,x} is a smooth bump function centered at x with width ~1/κ. -/
def rawFieldEval (_mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  ω (uvMollifier κ x)

/-- Wick product :φ(x)ⁿ:_C for UV-regularized field φ_κ.
    This is Hₙ(φ_κ(x), c_κ(x)) where φ_κ(x) = rawFieldEval and c_κ(x) = C_κ(x,x). -/
def wickPower (n : ℕ) (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  wickMonomial n (regularizedPointCovariance mass κ) (rawFieldEval mass κ ω x)

/-- The quartic Wick product :φ⁴:_C.
    Explicitly: :φ(x)⁴: = φ(x)⁴ - 6c_κ(x)φ(x)² + 3c_κ(x)². -/
def wickFourth (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) : ℝ :=
  wickPower 4 mass κ ω x

/-! ## Wick product properties -/

/-- Helper: the regularized point covariance equals the GaussianField covariance
    when mass > 0. -/
theorem regularizedPointCovariance_eq_covariance (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    regularizedPointCovariance mass κ =
      GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ 0) (uvMollifier κ 0) := by
  simp [regularizedPointCovariance, hmass]

/-- The freeFieldMeasure is a probability measure (needed for integral_const). -/
instance freeFieldMeasure_isProbabilityMeasure (mass : ℝ) (hmass : 0 < mass) :
    IsProbabilityMeasure (freeFieldMeasure mass hmass) :=
  freeFieldMeasure_isProbability mass hmass

/-- At the origin, the regularized point covariance is exactly the Gaussian covariance
    of the mollifier used in its definition. -/
theorem regularizedPointCovariance_covariance_origin
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) :
    GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ 0) (uvMollifier κ 0) =
    regularizedPointCovariance mass κ := by
  simpa using (regularizedPointCovariance_eq_covariance mass hmass κ).symm

/-- wickMonomial n c is continuous (it's a polynomial). -/
theorem wickMonomial_continuous : ∀ (n : ℕ) (c : ℝ), Continuous (wickMonomial n c)
  | 0, c => by simp [wickMonomial]; exact continuous_const
  | 1, c => by simp [wickMonomial]; exact continuous_id
  | n + 2, c => by
    have h1 := wickMonomial_continuous (n + 1) c
    have h2 := wickMonomial_continuous n c
    show Continuous (fun x => x * wickMonomial (n + 1) c x - (↑n + 1) * c * wickMonomial n c x)
    exact (continuous_id.mul h1).sub (continuous_const.mul h2)

/-- wickMonomial satisfies the parity identity: He_n(-x; c) = (-1)^n He_n(x; c). -/
theorem wickMonomial_neg : ∀ (n : ℕ) (c x : ℝ),
    wickMonomial n c (-x) = (-1) ^ n * wickMonomial n c x
  | 0, c, x => by simp [wickMonomial]
  | 1, c, x => by simp [wickMonomial]
  | n + 2, c, x => by
    simp only [wickMonomial_succ_succ]
    rw [wickMonomial_neg (n + 1) c x, wickMonomial_neg n c x]; ring

/-- Negation of the raw field evaluation is definitional. -/
@[simp]
theorem rawFieldEval_neg (mass : ℝ) (κ : UVCutoff) (ω : FieldConfig2D)
    (x : Spacetime2D) :
    rawFieldEval mass κ (-ω) x = -(rawFieldEval mass κ ω x) := rfl

/-- Wick power at even degree is invariant under φ → -φ. -/
theorem wickPower_even_neg (n : ℕ) (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) :
    wickPower (2 * n) mass κ (-ω) x = wickPower (2 * n) mass κ ω x := by
  unfold wickPower
  rw [rawFieldEval_neg, wickMonomial_neg]; simp

/-- The quartic Wick power is invariant under φ → -φ. -/
@[simp]
theorem wickPower_four_neg (mass : ℝ) (κ : UVCutoff)
    (ω : FieldConfig2D) (x : Spacetime2D) :
    wickPower 4 mass κ (-ω) x = wickPower 4 mass κ ω x :=
  wickPower_even_neg 2 mass κ ω x

/-- E[(ω f)^2] = covariance(f, f). -/
private theorem integral_sq_eq_cov (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂(freeFieldMeasure mass hmass) =
    GaussianField.covariance (freeCovarianceCLM mass hmass) f f := by
  have : ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f := fun ω => by ring
  simp_rw [this]
  change ∫ ω, ω f * ω f ∂(measure (freeCovarianceCLM mass hmass)) = _
  exact cross_moment_eq_covariance _ f f

/-- E[(ω f)^4] = 3 c² where c = covariance(f, f). Proved via wick_recursive. -/
private theorem integral_fourth_eq (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂(freeFieldMeasure mass hmass) =
    3 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  have h4 : ∀ ω : FieldConfig2D, (ω f) ^ 4 = ω f * ∏ i : Fin 3, ω ((fun _ => f) i) := by
    intro ω; simp only [Fin.prod_univ_three]; ring
  simp_rw [h4]
  change ∫ ω, ω f * ∏ i : Fin 3, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T 2 f (fun _ => f)]
  simp only [Fin.prod_univ_two]
  simp only [(show @inner ℝ ell2' _ (T f) (T f) = c from rfl)]
  have hint : ∫ ω : Configuration TestFun2D, ω f * ω f ∂(measure T) = c :=
    cross_moment_eq_covariance T f f
  simp only [hint]; simp; ring

/-- Moment recursion: E[(ω f)^{n+2}] = (n+1) · c · E[(ω f)^n].
    Proved by applying Wick's theorem (`wick_recursive`) to the constant product. -/
private theorem moment_recursion (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (n + 2) ∂(freeFieldMeasure mass hmass) =
    (↑(n + 1) : ℝ) * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, (ω f) ^ n ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  -- Rewrite (ω f)^{n+2} as ω f * ∏_{Fin(n+1)} ω((fun _ => f) i)
  have hlhs : ∀ ω : FieldConfig2D, (ω f) ^ (n + 2) =
      ω f * ∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i) := by
    intro ω
    rw [show (∏ i : Fin (n + 1), ω ((fun _ : Fin (n + 1) => f) i)) = (ω f) ^ (n + 1) from
      Fin.prod_const (n + 1) (ω f)]
    ring
  simp_rw [hlhs]
  change ∫ ω, ω f * ∏ i, ω ((fun _ => f) i) ∂(measure T) = _
  rw [wick_recursive T n f (fun _ => f)]
  -- After wick_recursive + beta reduction, the goal is:
  -- ∑ j, inner ℝ (T f) (T f) * ∫ ω, ∏ i, ω f ∂(measure T) = (n+1) * c * ∫ ω, (ω f)^n ∂μ
  simp_rw [show @inner ℝ ell2' _ (T f) (T f) = c from rfl, Fin.prod_const]
  -- Now: ∑ j : Fin (n+1), c * ∫ ω, (ω f)^n ∂μ = (n+1) * c * ∫ ω, (ω f)^n ∂μ
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  -- Unify type annotations (Configuration TestFun2D = FieldConfig2D, measure T = freeFieldMeasure)
  change _ = (↑(n + 1) : ℝ) * c *
    ∫ ω : Configuration TestFun2D, (ω f) ^ n ∂(GaussianField.measure T)
  push_cast; ring

/-! ## Stein identity via formal polynomials

The Stein identity E[X · p(X)] = c · E[p'(X)] for X ~ N(0,c) is proved for formal
polynomials p ∈ ℝ[X] using `Polynomial.induction_on'`. The monomial case reduces
to `moment_recursion`, and the addition case follows from linearity of integration.
Combined with the Hermite derivative identity He'_{n+1}(x;c) = (n+1)·He_n(x;c),
this gives a uniform proof that E[He_n(X;c)] = 0 for all n ≥ 1. -/

open Polynomial in
/-- Formal polynomial version of wickMonomial, defined by the same recursion. -/
private def wickPoly : ℕ → ℝ → ℝ[X]
  | 0, _ => 1
  | 1, _ => X
  | n + 2, c => X * wickPoly (n + 1) c - C ((n + 1 : ℝ) * c) * wickPoly n c

open Polynomial in
/-- wickPoly evaluates to wickMonomial. -/
private theorem wickPoly_eval : ∀ (n : ℕ) (c x : ℝ),
    (wickPoly n c).eval x = wickMonomial n c x
  | 0, c, x => by simp [wickPoly, wickMonomial]
  | 1, c, x => by simp [wickPoly, wickMonomial]
  | n + 2, c, x => by
    simp only [wickPoly, wickMonomial_succ_succ, eval_sub, eval_mul, eval_X, eval_C]
    rw [wickPoly_eval (n + 1) c x, wickPoly_eval n c x]

open Polynomial in
/-- Hermite derivative identity for formal polynomials:
    d/dx [He_{n+1}(x;c)] = (n+1) · He_n(x;c). -/
private theorem wickPoly_derivative : ∀ (n : ℕ) (c : ℝ),
    (wickPoly (n + 1) c).derivative = C (↑(n + 1) : ℝ) * wickPoly n c
  | 0, c => by simp only [wickPoly, derivative_X]; rw [← map_one C]; simp
  | 1, c => by
    simp only [wickPoly, map_sub, derivative_mul, derivative_X, one_mul, mul_one, derivative_C,
      sub_zero]; norm_num; simp only [C_ofNat]; ring
  | n + 2, c => by
    have hunfold : wickPoly (n + 2 + 1) c =
        X * wickPoly (n + 2) c - C ((↑(n + 1) + 1) * c) * wickPoly (n + 1) c := rfl
    rw [hunfold, map_sub, derivative_mul, derivative_X, derivative_C_mul,
      wickPoly_derivative (n + 1) c, wickPoly_derivative n c, one_mul]
    set P := wickPoly (n + 2) c; set Q := wickPoly (n + 1) c; set R := wickPoly n c
    have hrec : X * Q = P + C ((↑n + 1) * c) * R := by
      have h : P = X * Q - C ((↑n + 1) * c) * R := rfl; linear_combination -h
    have hCeq : C (↑(n + 2) : ℝ) * C ((↑n + 1) * c) =
        C ((↑(n + 1) + 1) * c) * C (↑(n + 1) : ℝ) := by
      simp only [← C_mul]; congr 1; push_cast; ring
    have hCadd : (1 : ℝ[X]) + C (↑(n + 2) : ℝ) = C (↑(n + 2 + 1) : ℝ) := by
      rw [← map_one C, ← map_add]; congr 1; push_cast; ring
    linear_combination C (↑(n + 2) : ℝ) * hrec + R * hCeq + P * hCadd

/-- Powers of the Gaussian pairing are integrable. -/
private theorem power_integrable (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (n : ℕ) :
    Integrable (fun ω : FieldConfig2D => (ω f) ^ n) (freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  have h : ∀ ω : FieldConfig2D, (ω f) ^ n = ∏ i : Fin n, ω ((fun _ => f) i) := by
    intro ω; rw [Fin.prod_const]
  simp_rw [h]
  change Integrable (fun ω => ∏ i : Fin n, ω ((fun _ => f) i)) (measure T)
  exact product_integrable T n (fun _ => f)

open Polynomial in
/-- Any polynomial evaluated at a Gaussian pairing is integrable. -/
private theorem poly_eval_integrable (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D)
    (p : ℝ[X]) :
    Integrable (fun ω : FieldConfig2D => p.eval (ω f)) (freeFieldMeasure mass hmass) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => exact (hp.add hq).congr (.of_forall fun ω => eval_add.symm)
  | monomial n a =>
    simp only [eval_monomial]
    exact (power_integrable mass hmass f n).const_mul a |>.congr
      (.of_forall fun ω => by ring)

open Polynomial in
/-- Stein identity for formal polynomials: E[X · p(X)] = c · E[p'(X)]
    where X = ω(f) under the Gaussian field measure and c = Cov(f,f).
    Proved by structural induction on polynomials: the monomial case
    reduces to `moment_recursion` and the addition case uses linearity. -/
private theorem stein_polynomial (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D)
    (p : ℝ[X]) :
    ∫ ω : FieldConfig2D, (ω f) * p.eval (ω f) ∂(freeFieldMeasure mass hmass) =
    GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
      ∫ ω : FieldConfig2D, p.derivative.eval (ω f) ∂(freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    simp only [eval_add, derivative_add]
    -- Integrability of X * p.eval(X): it's (X*p).eval(X) which is a polynomial eval
    have hfp : Integrable (fun ω : FieldConfig2D => (ω f) * eval (ω f) p)
        (freeFieldMeasure mass hmass) :=
      (poly_eval_integrable mass hmass f (X * p)).congr
        (.of_forall fun ω => by simp [eval_mul, eval_X])
    have hfq : Integrable (fun ω : FieldConfig2D => (ω f) * eval (ω f) q)
        (freeFieldMeasure mass hmass) :=
      (poly_eval_integrable mass hmass f (X * q)).congr
        (.of_forall fun ω => by simp [eval_mul, eval_X])
    have hdp : Integrable (fun ω : FieldConfig2D => eval (ω f) (derivative p))
        (freeFieldMeasure mass hmass) := poly_eval_integrable mass hmass f (derivative p)
    have hdq : Integrable (fun ω : FieldConfig2D => eval (ω f) (derivative q))
        (freeFieldMeasure mass hmass) := poly_eval_integrable mass hmass f (derivative q)
    simp_rw [mul_add]
    rw [integral_add hfp hfq, integral_add hdp hdq, mul_add, hp, hq]
  | monomial n a =>
    simp only [eval_monomial, derivative_monomial]
    -- ∫ (ωf) * (a * (ωf)^n) = c * ∫ (a * ↑n) * (ωf)^{n-1}
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) * (a * (ω f) ^ n) = a * (ω f) ^ (n + 1) from
      fun ω => by ring]
    rw [integral_const_mul, integral_const_mul]
    rcases n with _ | n
    · -- n = 0: a * ∫ (ωf) = 0
      simp only [Nat.cast_zero, mul_zero, zero_mul, Nat.zero_add, pow_one]
      have h0 : ∫ ω : FieldConfig2D, ω f ∂(freeFieldMeasure mass hmass) = 0 :=
        measure_centered T f
      rw [h0, mul_zero]
    · -- n ≥ 1: a * E[X^{n+2}] = c * (a * (n+1)) * E[X^n]
      rw [show n + 1 - 1 = n from by omega]
      rw [moment_recursion mass hmass f n]
      push_cast; ring

/-- Odd moments of the Gaussian field vanish: E[(ω f)^{2k+1}] = 0. -/
private theorem odd_power_vanish (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (k : ℕ) :
    ∫ ω : FieldConfig2D, (ω f) ^ (2 * k + 1) ∂(freeFieldMeasure mass hmass) = 0 := by
  have hprod : ∀ ω : FieldConfig2D, (ω f) ^ (2 * k + 1) =
    ∏ i : Fin (2 * k + 1), ω ((fun _ => f) i) := by
    intro ω; rw [Fin.prod_const]
  simp_rw [hprod]
  change ∫ ω, ∏ i : Fin (2 * k + 1), ω ((fun _ => f) i)
    ∂(measure (freeCovarianceCLM mass hmass)) = 0
  exact odd_moment_vanish _ k (fun _ => f)

/-- Centered Gaussian is symmetric under negation. -/
private theorem gaussianReal_zero_neg_invariant (v : ℝ≥0) :
    (gaussianReal 0 v).map (fun x : ℝ => -x) = gaussianReal 0 v := by
  rw [gaussianReal_map_neg]; simp

/-- Odd functions integrate to 0 under centered Gaussian. -/
private theorem integral_odd_gaussianReal_zero (v : ℝ≥0) (g : ℝ → ℝ)
    (hg_meas : Measurable g) (hg_odd : ∀ x, g (-x) = -g x) :
    ∫ x, g x ∂(gaussianReal 0 v) = 0 := by
  have h : ∫ x, g x ∂(gaussianReal 0 v) =
    ∫ x, g (-x) ∂(gaussianReal 0 v) := by
    conv_lhs => rw [← gaussianReal_zero_neg_invariant v]
    rw [integral_map measurable_neg.aemeasurable hg_meas.aestronglyMeasurable]
  simp only [hg_odd, integral_neg] at h; linarith

/-- wickMonomial n c is an odd function when n is odd. -/
private theorem wickMonomial_odd_fun (n : ℕ) (c : ℝ) (hn : Odd n) :
    ∀ x, wickMonomial n c (-x) = -wickMonomial n c x := by
  intro x; rw [wickMonomial_neg n c x]
  obtain ⟨k, rfl⟩ := hn; simp [pow_succ, pow_mul]

/-- For odd n, E[wickMonomial n c (ω f)] = 0 for ANY c.
    Proved via pushforward to 1D Gaussian + odd function symmetry. -/
private theorem wickMonomial_odd_zero_expectation (n : ℕ) (c : ℝ) (hn : Odd n)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω, wickMonomial n c (ω f) ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  rw [show freeFieldMeasure mass hmass = measure T from rfl,
    ← integral_map (configuration_eval_measurable f).aemeasurable
      (wickMonomial_continuous n c).measurable.aestronglyMeasurable,
    pairing_is_gaussian T f]
  exact integral_odd_gaussianReal_zero _ _ (wickMonomial_continuous n c).measurable
    (wickMonomial_odd_fun n c hn)

open Polynomial in
/-- E[wickMonomial (m+2) c X] = 0 via the Stein identity (no induction needed).
    The proof uses the identity He_{m+2}(x;c) = x·He_{m+1}(x;c) - (m+1)c·He_m(x;c),
    combined with E[X·p(X)] = c·E[p'(X)] and He'_{m+1} = (m+1)·He_m.
    The two terms cancel exactly, giving 0 regardless of E[He_m]. -/
private theorem wickMonomial_zero_expectation_ge_two (m : ℕ)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω : FieldConfig2D, wickMonomial (m + 2)
      (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) (ω f)
      ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  set μ := freeFieldMeasure mass hmass
  -- Step 1: Unfold the wickMonomial recursion
  have hrec : ∀ ω : FieldConfig2D, wickMonomial (m + 2) c (ω f) =
      (ω f) * wickMonomial (m + 1) c (ω f) - (↑m + 1) * c * wickMonomial m c (ω f) :=
    fun ω => wickMonomial_succ_succ m c (ω f)
  simp_rw [hrec]
  -- Step 2: Integrability
  have hint_mul : Integrable (fun ω : FieldConfig2D => (ω f) * wickMonomial (m + 1) c (ω f)) μ :=
    (poly_eval_integrable mass hmass f (X * wickPoly (m + 1) c)).congr
      (.of_forall fun ω => by simp [eval_mul, eval_X, wickPoly_eval])
  have hint_low : Integrable (fun ω : FieldConfig2D => wickMonomial m c (ω f)) μ :=
    (poly_eval_integrable mass hmass f (wickPoly m c)).congr
      (.of_forall fun ω => by simp [wickPoly_eval])
  have hint_const : Integrable (fun ω : FieldConfig2D =>
      (↑m + 1) * c * wickMonomial m c (ω f)) μ :=
    hint_low.const_mul ((↑m + 1) * c)
  -- Step 3: Split the integral
  rw [integral_sub hint_mul hint_const, integral_const_mul]
  -- Step 4: Apply Stein identity to wickPoly (m+1) c
  have hstein : ∫ ω : FieldConfig2D, (ω f) * wickMonomial (m + 1) c (ω f) ∂μ =
      c * ∫ ω : FieldConfig2D, (wickPoly (m + 1) c).derivative.eval (ω f) ∂μ := by
    have := stein_polynomial mass hmass f (wickPoly (m + 1) c)
    simp_rw [wickPoly_eval] at this; exact this
  rw [hstein]
  -- Step 5: Use the derivative identity and cancel
  simp_rw [wickPoly_derivative, eval_mul, eval_C, wickPoly_eval, integral_const_mul]
  push_cast; ring

/-- E[wickMonomial n c (ω f)] = 0 when c = covariance(f, f) and n ≥ 1.
    Odd n: Gaussian symmetry (odd function under symmetric measure).
    Even n ≥ 2: Stein identity + Hermite derivative identity. -/
theorem wickMonomial_zero_expectation (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) :
    ∫ ω, wickMonomial n
      (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) (ω f)
      ∂(freeFieldMeasure mass hmass) = 0 := by
  set T := freeCovarianceCLM mass hmass
  set c := GaussianField.covariance T f f
  -- Split on parity: odd n handled uniformly, even n by direct computation
  rcases Nat.even_or_odd n with ⟨k, hk⟩ | hodd
  · -- Even case: n = k + k
    rcases k with _ | _ | _ | k
    · omega
    · -- k = 1, n = 2
      have hn2 : n = 2 := by omega
      subst hn2; simp only [wickMonomial_two]
      rw [integral_sub
        (by have h := (pairing_memLp T f 2).integrable_norm_rpow
              (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
            refine h.congr (.of_forall fun ω => ?_)
            simp only [Real.norm_eq_abs]
            rw [show ((2 : ℝ≥0) : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num,
              Real.rpow_natCast, sq_abs])
        (integrable_const c)]
      rw [integral_sq_eq_cov mass hmass f, integral_const]
      simp [Measure.real, measure_univ]; ring
    · -- k = 2, n = 4
      have hn4 : n = 4 := by omega
      subst hn4; simp only [wickMonomial_four]
      -- Integrability helpers
      have hint4 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4)
          (freeFieldMeasure mass hmass) := by
        have h := (pairing_memLp T f 4).integrable_norm_rpow
          (show (4 : ℝ≥0∞) ≠ 0 by norm_num) (show (4 : ℝ≥0∞) ≠ ⊤ by norm_num)
        refine h.congr (.of_forall fun ω => ?_)
        simp only [Real.norm_eq_abs]
        rw [show ((4 : ℝ≥0) : ℝ≥0∞).toReal = ((4 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast]
        have : (ω f) ^ 2 = |ω f| ^ 2 := (sq_abs (ω f)).symm
        nlinarith [sq_nonneg (ω f), sq_nonneg (|ω f|)]
      have hint2 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2)
          (freeFieldMeasure mass hmass) := by
        have h := (pairing_memLp T f 2).integrable_norm_rpow
          (show (2 : ℝ≥0∞) ≠ 0 by norm_num) (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num)
        refine h.congr (.of_forall fun ω => ?_)
        simp only [Real.norm_eq_abs]
        rw [show ((2 : ℝ≥0) : ℝ≥0∞).toReal = ((2 : ℕ) : ℝ) from by norm_num,
          Real.rpow_natCast, sq_abs]
      -- Compute: ∫ (x⁴ - 6cx² + 3c²) = 3c² - 6c·c + 3c² = 0
      -- Split the integral using have+exact (rw can't match the pattern)
      have split1 : ∫ ω : FieldConfig2D,
          ((ω f) ^ 4 - 6 * c * (ω f) ^ 2 + 3 * c ^ 2) ∂(freeFieldMeasure mass hmass) =
          (∫ ω : FieldConfig2D, ((ω f) ^ 4 - 6 * c * (ω f) ^ 2)
            ∂(freeFieldMeasure mass hmass)) +
          ∫ _ : FieldConfig2D, (3 * c ^ 2) ∂(freeFieldMeasure mass hmass) :=
        integral_add (hint4.sub (hint2.const_mul _)) (integrable_const _)
      have split2 : ∫ ω : FieldConfig2D,
          ((ω f) ^ 4 - 6 * c * (ω f) ^ 2) ∂(freeFieldMeasure mass hmass) =
          (∫ ω : FieldConfig2D, (ω f) ^ 4 ∂(freeFieldMeasure mass hmass)) -
          ∫ ω : FieldConfig2D, (6 * c * (ω f) ^ 2) ∂(freeFieldMeasure mass hmass) :=
        integral_sub hint4 (hint2.const_mul _)
      rw [split1, split2, integral_const_mul,
        integral_fourth_eq mass hmass f, integral_sq_eq_cov mass hmass f, integral_const]
      simp [Measure.real, measure_univ]; ring
    · -- k ≥ 3, n ≥ 6: apply the Stein identity lemma
      have hn_eq : n = (2 * k + 4) + 2 := by omega
      rw [hn_eq]
      exact wickMonomial_zero_expectation_ge_two _ mass hmass f
  · -- Odd case: use Gaussian symmetry (works for any c)
    exact wickMonomial_odd_zero_expectation n c hodd mass hmass f

/-- Wick products have zero expectation once the Wick covariance parameter matches
    the variance of the smeared Gaussian variable at the evaluation point. -/
theorem wickPower_zero_expectation (n : ℕ) (hn : 0 < n)
    (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff) (x : Spacetime2D)
    (hcov : GaussianField.covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ x) (uvMollifier κ x) = regularizedPointCovariance mass κ) :
    ∫ ω, wickPower n mass κ ω x ∂(freeFieldMeasure mass hmass) = 0 := by
  set f := uvMollifier κ x
  set c := regularizedPointCovariance mass κ
  set T := freeCovarianceCLM mass hmass
  have hc : c = GaussianField.covariance T f f :=
    by simpa [f, c, T] using hcov.symm
  show ∫ ω, wickMonomial n c (ω f) ∂(freeFieldMeasure mass hmass) = 0
  rw [hc]
  exact wickMonomial_zero_expectation n hn mass hmass f

/-- Hölder triple: `(2p)⁻¹ + (2p)⁻¹ = p⁻¹`. Used for products via Hölder's inequality. -/
instance holderTriple_double (p : ℝ≥0∞) : ENNReal.HolderTriple (2 * p) (2 * p) p where
  inv_add_inv_eq_inv := by
    by_cases h0 : p = 0
    · simp [h0]
    · by_cases htop : p = ⊤
      · simp [htop]
      · have h2p_inv : (2 * p)⁻¹ = 2⁻¹ * p⁻¹ :=
          ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
        rw [h2p_inv, ← two_mul,
          show (2 : ℝ≥0∞) * (2⁻¹ * p⁻¹) = (2 * 2⁻¹) * p⁻¹ from by ring]
        rw [ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

/-- Wick monomials composed with an Lᵖ function are in Lᵖ for all finite p.
    Proof by structural induction matching the wickMonomial recursion,
    using Hölder's inequality at each step. -/
theorem wickMonomial_memLp_all
    {μ : Measure FieldConfig2D} [IsFiniteMeasure μ]
    (c : ℝ) (g : FieldConfig2D → ℝ)
    (hg : ∀ q : ℝ≥0∞, q ≠ ⊤ → MemLp g q μ) :
    ∀ (n : ℕ) (p : ℝ≥0∞), p ≠ ⊤ → MemLp (fun ω => wickMonomial n c (g ω)) p μ
  | 0, p, _ => by simp; exact memLp_const 1
  | 1, p, hp => by simp; exact hg p hp
  | n + 2, p, hp => by
    have h2p : 2 * p ≠ ⊤ := ENNReal.mul_ne_top (by norm_num) hp
    have ih_n := wickMonomial_memLp_all c g hg n
    have ih_n1 := wickMonomial_memLp_all c g hg (n + 1)
    set h := fun ω => wickMonomial (n + 1) c (g ω) with hdef
    have hprod : MemLp (g * h) p μ := (ih_n1 (2 * p) h2p).mul (hg (2 * p) h2p)
    have hconst : MemLp (((↑n + 1) * c) • fun ω => wickMonomial n c (g ω)) p μ :=
      (ih_n p hp).const_smul ((↑n + 1) * c)
    have hsub : MemLp (g * h - ((↑n + 1) * c) • fun ω => wickMonomial n c (g ω)) p μ :=
      hprod.sub hconst
    refine (memLp_congr_ae (Filter.Eventually.of_forall fun ω => ?_)).mp hsub
    simp only [wickMonomial_succ_succ, hdef, Pi.mul_apply, Pi.sub_apply, Pi.smul_apply,
      smul_eq_mul]

/-- Specialization of `wickMonomial_memLp_all` to a Gaussian pairing `ω(f)`. -/
theorem wickMonomial_memLp
    (n : ℕ) (mass : ℝ) (hmass : 0 < mass) (f : TestFun2D) (c : ℝ)
    {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω : FieldConfig2D => wickMonomial n c (ω f)) p
      (freeFieldMeasure mass hmass) := by
  set T := freeCovarianceCLM mass hmass
  apply wickMonomial_memLp_all c (fun ω : FieldConfig2D => ω f)
  · intro q hq
    have h := pairing_memLp T f q.toNNReal
    rwa [ENNReal.coe_toNNReal hq] at h
  · exact hp

/-- Wick products are in Lᵖ for all p < ∞ in d=2.
    This is Theorem 8.5.3 of Glimm-Jaffe.
    The proof uses Hölder's inequality via induction on the wickMonomial recursion,
    combined with the fact that Gaussian pairings ω(f) have all finite moments. -/
theorem wickPower_memLp (n : ℕ) (mass : ℝ) (hmass : 0 < mass) (κ : UVCutoff)
    (x : Spacetime2D) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (fun ω => wickPower n mass κ ω x) p (freeFieldMeasure mass hmass) := by
  set f := uvMollifier κ x
  set c := regularizedPointCovariance mass κ
  show MemLp (fun ω => wickMonomial n c (ω f)) p (freeFieldMeasure mass hmass)
  simpa [f, c] using wickMonomial_memLp n mass hmass f c hp

/-- Finite `0/2/4` Wick cylinder polynomial. This is the natural algebraic shape
of the finite-dimensional approximants expected in the Nelson branch. -/
def finiteWickCylinder
    {ι : Type*} [Fintype ι]
    (a4 a2 : ι → ℝ) (c4 c2 : ι → ℝ) (f4 f2 : ι → TestFun2D)
    (a0 : ℝ) (ω : FieldConfig2D) : ℝ :=
  (∑ i, a4 i * wickMonomial 4 (c4 i) (ω (f4 i))) +
    (∑ i, a2 i * wickMonomial 2 (c2 i) (ω (f2 i))) + a0

/-- A real-valued random variable is a finite Wick cylinder if it is given by a
finite `0/2/4` Wick polynomial. This is the natural algebraic class expected in
finite-dimensional approximants to the Nelson branch. -/
def IsFiniteWickCylinder (Z : FieldConfig2D → ℝ) : Prop :=
  ∃ n : ℕ, ∃
      (a4 a2 c4 c2 : Fin n → ℝ) (f4 f2 : Fin n → TestFun2D) (a0 : ℝ),
    Z = finiteWickCylinder a4 a2 c4 c2 f4 f2 a0

/-- Finite Wick cylinder polynomials built from quartic and quadratic Wick
monomials, plus a constant term, are in `L^p` for every finite `p`.

This is the natural algebraic shape of Riemann-sum approximants to the
cutoff-interaction differences that appear in Nelson's argument. -/
theorem finiteWickCylinder_memLp
    {ι : Type*} [Fintype ι]
    (mass : ℝ) (hmass : 0 < mass)
    (a4 a2 : ι → ℝ) (c4 c2 : ι → ℝ) (f4 f2 : ι → TestFun2D)
    (a0 : ℝ) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp (finiteWickCylinder a4 a2 c4 c2 f4 f2 a0) p (freeFieldMeasure mass hmass) := by
  classical
  let μ := freeFieldMeasure mass hmass
  have h4 : MemLp
      (fun ω : FieldConfig2D => ∑ i, a4 i * wickMonomial 4 (c4 i) (ω (f4 i))) p μ := by
    simpa using
      (memLp_finset_sum (μ := μ) (p := p) (s := (Finset.univ : Finset ι))
        (f := fun i ω => a4 i * wickMonomial 4 (c4 i) (ω (f4 i)))
        (fun i _ => by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (wickMonomial_memLp 4 mass hmass (f4 i) (c4 i) hp).const_smul (a4 i)))
  have h2 : MemLp
      (fun ω : FieldConfig2D => ∑ i, a2 i * wickMonomial 2 (c2 i) (ω (f2 i))) p μ := by
    simpa using
      (memLp_finset_sum (μ := μ) (p := p) (s := (Finset.univ : Finset ι))
        (f := fun i ω => a2 i * wickMonomial 2 (c2 i) (ω (f2 i)))
        (fun i _ => by
          simpa [Pi.smul_apply, smul_eq_mul] using
            (wickMonomial_memLp 2 mass hmass (f2 i) (c2 i) hp).const_smul (a2 i)))
  simpa only [finiteWickCylinder] using (h4.add h2).add (memLp_const (μ := μ) (p := p) a0)

/-- Hence every finite Wick cylinder polynomial of the `0/2/4` type has all
even moments. -/
theorem finiteWickCylinder_even_integrable
    {ι : Type*} [Fintype ι]
    (mass : ℝ) (hmass : 0 < mass)
    (a4 a2 : ι → ℝ) (c4 c2 : ι → ℝ) (f4 f2 : ι → TestFun2D)
    (a0 : ℝ) (j : ℕ) :
    Integrable
      (fun ω : FieldConfig2D => |finiteWickCylinder a4 a2 c4 c2 f4 f2 a0 ω| ^ (2 * j))
      (freeFieldMeasure mass hmass) := by
  let μ := freeFieldMeasure mass hmass
  by_cases hj : j = 0
  · subst hj
    simp
  · have hmem : MemLp
        (finiteWickCylinder a4 a2 c4 c2 f4 f2 a0)
        ((2 * j : ℕ) : ℝ≥0∞) μ :=
      finiteWickCylinder_memLp mass hmass a4 a2 c4 c2 f4 f2 a0 ENNReal.coe_ne_top
    have hint : Integrable
        (fun ω : FieldConfig2D =>
          ‖finiteWickCylinder a4 a2 c4 c2 f4 f2 a0 ω‖ ^
            (((2 * j : ℕ) : ℝ≥0∞).toReal)) μ := by
      simpa using hmem.integrable_norm_rpow'
    convert hint using 1
    ext ω
    rw [show ((↑(2 * j) : ℝ≥0∞).toReal) = (2 * j : ℝ) by simp, Real.norm_eq_abs]
    have hcast : (2 * ↑j : ℝ) = ↑(2 * j) := by
      exact_mod_cast (show 2 * j = 2 * j by rfl)
    rw [hcast, Real.rpow_natCast]

/-- Every finite Wick cylinder polynomial is in `L^p` for finite `p`. -/
theorem IsFiniteWickCylinder.memLp
    {Z : FieldConfig2D → ℝ} (hZ : IsFiniteWickCylinder Z)
    (mass : ℝ) (hmass : 0 < mass) {p : ℝ≥0∞} (hp : p ≠ ⊤) :
    MemLp Z p (freeFieldMeasure mass hmass) := by
  rcases hZ with ⟨n, a4, a2, c4, c2, f4, f2, a0, rfl⟩
  exact finiteWickCylinder_memLp mass hmass a4 a2 c4 c2 f4 f2 a0 hp

/-- Every finite Wick cylinder polynomial has all even moments. -/
theorem IsFiniteWickCylinder.even_integrable
    {Z : FieldConfig2D → ℝ} (hZ : IsFiniteWickCylinder Z)
    (mass : ℝ) (hmass : 0 < mass) (j : ℕ) :
    Integrable (fun ω : FieldConfig2D => |Z ω| ^ (2 * j)) (freeFieldMeasure mass hmass) := by
  rcases hZ with ⟨n, a4, a2, c4, c2, f4, f2, a0, rfl⟩
  exact finiteWickCylinder_even_integrable mass hmass a4 a2 c4 c2 f4 f2 a0 j

/-- A `finiteWickCylinder` built on any finite index type is, tautologically, a
finite Wick cylinder in the `Fin n`-encoded sense. This bridge lets later
infrastructure work with natural finite index types (for example lattice cells)
without re-encoding them by hand. -/
theorem finiteWickCylinder_isFinite
    {ι : Type*} [Fintype ι]
    (a4 a2 : ι → ℝ) (c4 c2 : ι → ℝ) (f4 f2 : ι → TestFun2D) (a0 : ℝ) :
    IsFiniteWickCylinder (finiteWickCylinder a4 a2 c4 c2 f4 f2 a0) := by
  classical
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  refine ⟨Fintype.card ι,
    (fun i => a4 (e.symm i)),
    (fun i => a2 (e.symm i)),
    (fun i => c4 (e.symm i)),
    (fun i => c2 (e.symm i)),
    (fun i => f4 (e.symm i)),
    (fun i => f2 (e.symm i)),
    a0, ?_⟩
  ext ω
  have h4 :
      (∑ x, a4 (e.symm x) * wickMonomial 4 (c4 (e.symm x)) (ω (f4 (e.symm x)))) =
        ∑ i, a4 i * wickMonomial 4 (c4 i) (ω (f4 i)) :=
    (Fintype.sum_equiv e
      (fun i => a4 i * wickMonomial 4 (c4 i) (ω (f4 i)))
      (fun i => a4 (e.symm i) * wickMonomial 4 (c4 (e.symm i)) (ω (f4 (e.symm i))))
      (fun i => by simp)).symm
  have h2 :
      (∑ x, a2 (e.symm x) * wickMonomial 2 (c2 (e.symm x)) (ω (f2 (e.symm x)))) =
        ∑ i, a2 i * wickMonomial 2 (c2 i) (ω (f2 i)) :=
    (Fintype.sum_equiv e
      (fun i => a2 i * wickMonomial 2 (c2 i) (ω (f2 i)))
      (fun i => a2 (e.symm i) * wickMonomial 2 (c2 (e.symm i)) (ω (f2 (e.symm i))))
      (fun i => by simp)).symm
  simp only [finiteWickCylinder]
  rw [h4, h2]

/-- Honest frontier for Nelson-type hypercontractive comparison on degree-4
finite Wick cylinders.

This isolates the genuine Gaussian-polynomial inequality needed downstream: any
finite linear combination of quadratic and quartic Wick monomials under the free
field measure should satisfy a dimension-free even-moment comparison with degree
`4` growth `(C j)^(4j)`. The canonical Nelson uniform approximants are already
instances of `IsFiniteWickCylinder`, so this is the real remaining
hypercontractive leaf rather than sequence-specific bookkeeping. -/
theorem gap_finiteWickCylinder_even_moment_comparison
    (mass : ℝ) (hmass : 0 < mass) :
    ∃ C : ℝ, 0 < C ∧
      ∀ {Z : FieldConfig2D → ℝ}, IsFiniteWickCylinder Z →
        ∀ (j : ℕ), 0 < j →
          ∫ ω, |Z ω| ^ (2 * j) ∂(freeFieldMeasure mass hmass)
            ≤ (C * ↑j) ^ (4 * j) *
                (∫ ω, (Z ω) ^ 2 ∂(freeFieldMeasure mass hmass)) ^ j := by
  sorry

/-! ## Re-Wick-ordering under change of covariance

When the covariance changes from `c₁` to `c₂`, the Wick monomials transform via:

  `:xⁿ:_{c₁} = Σₖ C(n,2k)(2k-1)!!(-1)ᵏ(c₁-c₂)ᵏ :x^{n-2k}:_{c₂}`

This is the Hermite polynomial addition theorem. For the cases we need:
  `:x²:_{c₁} = :x²:_{c₂} - (c₁ - c₂)`
  `:x⁴:_{c₁} = :x⁴:_{c₂} - 6(c₁-c₂):x²:_{c₂} + 3(c₁-c₂)²`

These are pure algebraic identities, proved by expanding and using `ring`.
-/

/-- **Re-Wick-ordering for the quartic** (Hermite addition theorem, Glimm-Jaffe 8.6.1):
    :x⁴:_{c₁} = :x⁴:_{c₂} - 6(c₁-c₂) :x²:_{c₂} + 3(c₁-c₂)²

    This is a purely algebraic identity between probabilists' Hermite polynomials.
    Note the sign: the middle term has a minus when δc = c₁ - c₂. -/
theorem wickMonomial_rewick_four (c₁ c₂ x : ℝ) :
    wickMonomial 4 c₁ x =
      wickMonomial 4 c₂ x - 6 * (c₁ - c₂) * wickMonomial 2 c₂ x
      + 3 * (c₁ - c₂) ^ 2 := by
  simp [wickMonomial_four, wickMonomial_two]; ring

/-- Difference factorization for the quartic Wick polynomial at fixed variance.
    This isolates one factor of `x - y`, which is the useful form for UV shell
    increment estimates. -/
theorem wickMonomial_four_diff_factor (c x y : ℝ) :
    wickMonomial 4 c x - wickMonomial 4 c y =
      (x - y) * (x ^ 3 + x ^ 2 * y + x * y ^ 2 + y ^ 3 - 6 * c * (x + y)) := by
  simp [wickMonomial_four]
  ring

/-- The raw field increment is evaluation on the mollifier difference. -/
theorem rawFieldEval_sub
    (mass : ℝ) (κ₁ κ₂ : UVCutoff) (ω : FieldConfig2D) (x : Spacetime2D) :
    rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x =
      ω (uvMollifier κ₂ x - uvMollifier κ₁ x) := by
  simp [rawFieldEval]

/-- Covariance of a difference of test functions expanded as a quadratic form. -/
theorem covariance_sub_self
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    GaussianField.covariance (freeCovarianceCLM mass hmass) (f - g) (f - g) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f f
      - 2 * GaussianField.covariance (freeCovarianceCLM mass hmass) f g
      + GaussianField.covariance (freeCovarianceCLM mass hmass) g g := by
  simp [GaussianField.covariance, norm_sub_sq_real]

/-- The second moment of the raw-field increment equals the covariance of the
    corresponding mollifier difference. This is the basic Gaussian identity
    behind shellwise `L²` estimates. -/
theorem rawFieldEval_sub_sq_expectation
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    ∫ ω : FieldConfig2D,
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) ^ 2
        ∂(freeFieldMeasure mass hmass)
    = GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)
        (uvMollifier κ₂ x - uvMollifier κ₁ x) := by
  have hfun :
      (fun ω : FieldConfig2D => (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) ^ 2) =
      (fun ω : FieldConfig2D => (ω (uvMollifier κ₂ x - uvMollifier κ₁ x)) ^ 2) := by
    ext ω
    rw [rawFieldEval_sub]
  rw [hfun]
  have hsq :
      (fun ω : FieldConfig2D => (ω (uvMollifier κ₂ x - uvMollifier κ₁ x)) ^ 2) =
      (fun ω : FieldConfig2D =>
        ω (uvMollifier κ₂ x - uvMollifier κ₁ x) *
          ω (uvMollifier κ₂ x - uvMollifier κ₁ x)) := by
    ext ω
    ring
  rw [hsq, freeFieldMeasure]
  simpa [GaussianField.covariance] using
    (cross_moment_eq_covariance (freeCovarianceCLM mass hmass)
      (uvMollifier κ₂ x - uvMollifier κ₁ x)
      (uvMollifier κ₂ x - uvMollifier κ₁ x))

/-- The fourth moment of the raw-field increment is the Gaussian fourth-moment
    polynomial in the covariance of the mollifier difference. This is the
    quantitative input behind Hölder/Cauchy-Schwarz bounds for the quartic
    shell increment. -/
theorem rawFieldEval_sub_fourth_expectation
    (mass : ℝ) (hmass : 0 < mass) (κ₁ κ₂ : UVCutoff) (x : Spacetime2D) :
    ∫ ω : FieldConfig2D,
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) ^ 4
        ∂(freeFieldMeasure mass hmass)
    = 3 * (GaussianField.covariance (freeCovarianceCLM mass hmass)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)
        (uvMollifier κ₂ x - uvMollifier κ₁ x)) ^ 2 := by
  set f : TestFun2D := uvMollifier κ₂ x - uvMollifier κ₁ x
  have hsub : (fun ω : FieldConfig2D =>
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) ^ 4) =
    (fun ω : FieldConfig2D => (ω f) ^ 4) := by
    ext ω
    simpa [f] using congrArg (fun t : ℝ => t ^ 4) (rawFieldEval_sub mass κ₁ κ₂ ω x)
  rw [hsub]
  have h2 : ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂(freeFieldMeasure mass hmass) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f f := by
    simp_rw [show ∀ ω : FieldConfig2D, (ω f) ^ 2 = ω f * ω f from fun ω => by ring]
    exact cross_moment_eq_covariance _ f f
  rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion mass hmass f 2, h2]
  push_cast
  ring

/-- Mixed fourth moment `E[X²Y²]` for Gaussian linear observables. -/
theorem mixed_fourth_moment_two_two
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 2 * (ω g) ^ 2 ∂(freeFieldMeasure mass hmass) =
      GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
        GaussianField.covariance (freeCovarianceCLM mass hmass) g g
      + 2 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2 := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cgg := GaussianField.covariance T g g
  let cfg := GaussianField.covariance T f g
  have hsplit : ∀ ω : FieldConfig2D,
      (ω f) ^ 2 * (ω g) ^ 2 = ω f * ∏ i : Fin 3, ω (![f, g, g] i) := by
    intro ω
    simp [Fin.prod_univ_three]
    ring
  simp_rw [hsplit]
  change ∫ ω : Configuration TestFun2D, ω f * ∏ i : Fin 3, ω (![f, g, g] i) ∂(measure T) =
      cff * cgg + 2 * cfg ^ 2
  rw [wick_recursive T 2 f (fun i => (![f, g, g] : Fin 3 → TestFun2D) i)]
  have hff : ∫ ω : Configuration TestFun2D, ω f * ω f ∂(measure T) = cff := by
    simpa [GaussianField.covariance, cff] using cross_moment_eq_covariance T f f
  have hgg : ∫ ω : Configuration TestFun2D, ω g * ω g ∂(measure T) = cgg := by
    simpa [GaussianField.covariance, cgg] using cross_moment_eq_covariance T g g
  have hfg' : ∫ ω : Configuration TestFun2D, ω f * ω g ∂(measure T) = cfg := by
    simpa [GaussianField.covariance, cfg] using cross_moment_eq_covariance T f g
  have hlast :
      ∫ ω : Configuration TestFun2D, ω f * ω (![f, g, g] (Fin.succAbove 2 1)) ∂(measure T) = cfg := by
    simpa [GaussianField.covariance, cfg] using cross_moment_eq_covariance T f g
  rw [Fin.sum_univ_three]
  simp [cff, cgg, cfg, hgg, hfg', hlast, GaussianField.covariance]
  ring

/-- Mixed fourth moment `E[X^3 Y]` for Gaussian linear observables. -/
theorem mixed_fourth_moment_three_one
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 3 * (ω g) ∂(freeFieldMeasure mass hmass) =
      3 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
        GaussianField.covariance (freeCovarianceCLM mass hmass) f g := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cfg := GaussianField.covariance T f g
  have hsplit : ∀ ω : FieldConfig2D,
      (ω f) ^ 3 * (ω g) = ω f * ∏ i : Fin 3, ω (![f, f, g] i) := by
    intro ω
    simp [Fin.prod_univ_three]
    ring
  simp_rw [hsplit]
  change ∫ ω : Configuration TestFun2D, ω f * ∏ i : Fin 3, ω (![f, f, g] i) ∂(measure T) =
      3 * cff * cfg
  rw [wick_recursive T 2 f (fun i => (![f, f, g] : Fin 3 → TestFun2D) i)]
  have hff : ∫ ω : Configuration TestFun2D, ω f * ω f ∂(measure T) = cff := by
    simpa [GaussianField.covariance, cff] using cross_moment_eq_covariance T f f
  have hfg : ∫ ω : Configuration TestFun2D, ω f * ω g ∂(measure T) = cfg := by
    simpa [GaussianField.covariance, cfg] using cross_moment_eq_covariance T f g
  have hlast :
      ∫ ω : Configuration TestFun2D, ω f * ω (![f, f, g] (Fin.succAbove 2 1)) ∂(measure T) = cff := by
    simpa [GaussianField.covariance, cff] using cross_moment_eq_covariance T f f
  rw [Fin.sum_univ_three]
  simp [cff, cfg, hfg, hlast, GaussianField.covariance]
  ring

/-- Mixed sixth moment `E[X^4 Y^2]` for Gaussian linear observables. -/
theorem mixed_sixth_moment_four_two
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 4 * (ω g) ^ 2 ∂(freeFieldMeasure mass hmass) =
      3 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 *
          GaussianField.covariance (freeCovarianceCLM mass hmass) g g
      + 12 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
          (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2 := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cgg := GaussianField.covariance T g g
  let cfg := GaussianField.covariance T f g
  have hsplit : ∀ ω : FieldConfig2D,
      (ω f) ^ 4 * (ω g) ^ 2 = ω f * ∏ i : Fin 5, ω (![f, f, f, g, g] i) := by
    intro ω
    simp [Fin.prod_univ_five]
    ring
  simp_rw [hsplit]
  change ∫ ω : Configuration TestFun2D, ω f * ∏ i : Fin 5, ω (![f, f, f, g, g] i) ∂(measure T) =
      3 * cff ^ 2 * cgg + 12 * cff * cfg ^ 2
  rw [wick_recursive T 4 f (fun i => (![f, f, f, g, g] : Fin 5 → TestFun2D) i)]
  rw [Fin.sum_univ_five]
  have hdrop0 (i : Fin 4) :
      (![f, f, f, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 0 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop1 (i : Fin 4) :
      (![f, f, f, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 1 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop2 (i : Fin 4) :
      (![f, f, f, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 2 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop3 (i : Fin 4) :
      (![f, f, f, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 3 i) =
        (![f, f, f, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop4 (i : Fin 4) :
      (![f, f, f, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 4 i) =
        (![f, f, f, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hprod_ffgg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 4, ω ((![f, f, g, g] : Fin 4 → TestFun2D) i) =
        (ω f) ^ 2 * (ω g) ^ 2 := by
    intro ω
    simp [Fin.prod_univ_four]
    ring
  have hprod_fffg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 4, ω ((![f, f, f, g] : Fin 4 → TestFun2D) i) =
        (ω f) ^ 3 * (ω g) := by
    intro ω
    simp [Fin.prod_univ_four, pow_succ, mul_left_comm, mul_comm]
  have h42 :
      ∫ ω : Configuration TestFun2D, (ω f) ^ 2 * (ω g) ^ 2 ∂(measure T) =
        cff * cgg + 2 * cfg ^ 2 := by
    simpa [T, cff, cgg, cfg] using mixed_fourth_moment_two_two mass hmass f g
  have h31 :
      ∫ ω : Configuration TestFun2D, (ω f) ^ 3 * (ω g) ∂(measure T) =
        3 * cff * cfg := by
    simpa [T, cff, cfg] using mixed_fourth_moment_three_one mass hmass f g
  simp_rw [hdrop0, hdrop1, hdrop2, hdrop3, hdrop4]
  simp_rw [hprod_ffgg, hprod_fffg]
  simp [GaussianField.covariance, cff, cgg, cfg, h42, h31]
  ring

/-- Mixed sixth moment `E[X^3 Y^3]` for Gaussian linear observables. -/
theorem mixed_sixth_moment_three_three
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 3 * (ω g) ^ 3 ∂(freeFieldMeasure mass hmass) =
      9 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
          GaussianField.covariance (freeCovarianceCLM mass hmass) g g *
          GaussianField.covariance (freeCovarianceCLM mass hmass) f g
      + 6 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 3 := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cgg := GaussianField.covariance T g g
  let cfg := GaussianField.covariance T f g
  have hsplit : ∀ ω : FieldConfig2D,
      (ω f) ^ 3 * (ω g) ^ 3 = ω f * ∏ i : Fin 5, ω (![f, f, g, g, g] i) := by
    intro ω
    simp [Fin.prod_univ_five]
    ring
  simp_rw [hsplit]
  change ∫ ω : Configuration TestFun2D, ω f * ∏ i : Fin 5, ω (![f, f, g, g, g] i) ∂(measure T) =
      9 * cff * cgg * cfg + 6 * cfg ^ 3
  rw [wick_recursive T 4 f (fun i => (![f, f, g, g, g] : Fin 5 → TestFun2D) i)]
  rw [Fin.sum_univ_five]
  have hdrop0 (i : Fin 4) :
      (![f, f, g, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 0 i) =
        (![f, g, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop1 (i : Fin 4) :
      (![f, f, g, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 1 i) =
        (![f, g, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop2 (i : Fin 4) :
      (![f, f, g, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 2 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop3 (i : Fin 4) :
      (![f, f, g, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 3 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop4 (i : Fin 4) :
      (![f, f, g, g, g] : Fin 5 → TestFun2D) (Fin.succAbove 4 i) =
        (![f, f, g, g] : Fin 4 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hprod_fggg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 4, ω ((![f, g, g, g] : Fin 4 → TestFun2D) i) =
        (ω f) * (ω g) ^ 3 := by
    intro ω
    simp [Fin.prod_univ_four]
    ring
  have hprod_ffgg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 4, ω ((![f, f, g, g] : Fin 4 → TestFun2D) i) =
        (ω f) ^ 2 * (ω g) ^ 2 := by
    intro ω
    simp [Fin.prod_univ_four]
    ring
  have h22 :
      ∫ ω : Configuration TestFun2D, (ω f) ^ 2 * (ω g) ^ 2 ∂(measure T) =
        cff * cgg + 2 * cfg ^ 2 := by
    simpa [T, cff, cgg, cfg] using mixed_fourth_moment_two_two mass hmass f g
  have h13 :
      ∫ ω : Configuration TestFun2D, (ω f) * (ω g) ^ 3 ∂(measure T) =
        3 * cgg * cfg := by
    calc
      ∫ ω : Configuration TestFun2D, (ω f) * (ω g) ^ 3 ∂(measure T)
          = 3 * cgg * GaussianField.covariance T g f := by
              simpa [T, cgg, mul_comm] using mixed_fourth_moment_three_one mass hmass g f
      _ = 3 * cgg * cfg := by
            simp [cfg, GaussianField.covariance, real_inner_comm]
  simp_rw [hdrop0, hdrop1, hdrop2, hdrop3, hdrop4]
  simp_rw [hprod_fggg, hprod_ffgg]
  simp [GaussianField.covariance, cff, cgg, cfg, h22, h13]
  ring

/-- Mixed eighth moment `E[X^4 Y^4]` for Gaussian linear observables. -/
theorem mixed_eighth_moment_four_four
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) :
    ∫ ω : FieldConfig2D, (ω f) ^ 4 * (ω g) ^ 4 ∂(freeFieldMeasure mass hmass) =
      9 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 *
          (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 2
      + 72 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
          GaussianField.covariance (freeCovarianceCLM mass hmass) g g *
          (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2
      + 24 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 4 := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cgg := GaussianField.covariance T g g
  let cfg := GaussianField.covariance T f g
  have hsplit : ∀ ω : FieldConfig2D,
      (ω f) ^ 4 * (ω g) ^ 4 = ω f * ∏ i : Fin 7, ω (![f, f, f, g, g, g, g] i) := by
    intro ω
    simp [Fin.prod_univ_seven]
    ring
  simp_rw [hsplit]
  change ∫ ω : Configuration TestFun2D, ω f * ∏ i : Fin 7, ω (![f, f, f, g, g, g, g] i) ∂(measure T) =
      9 * cff ^ 2 * cgg ^ 2 + 72 * cff * cgg * cfg ^ 2 + 24 * cfg ^ 4
  rw [wick_recursive T 6 f (fun i => (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) i)]
  rw [Fin.sum_univ_seven]
  have h24 :
      ∫ ω : Configuration TestFun2D, (ω f) ^ 2 * (ω g) ^ 4 ∂(measure T) =
        3 * cff * cgg ^ 2 + 12 * cgg * cfg ^ 2 := by
    calc
      ∫ ω : Configuration TestFun2D, (ω f) ^ 2 * (ω g) ^ 4 ∂(measure T)
          = ∫ ω : Configuration TestFun2D, (ω g) ^ 4 * (ω f) ^ 2 ∂(measure T) := by
              congr with ω
              ring
      _ = 3 * cgg ^ 2 * cff + 12 * cgg * (GaussianField.covariance T g f) ^ 2 := by
            simpa [T, cff, cgg, mul_comm, mul_left_comm, mul_assoc] using
              mixed_sixth_moment_four_two mass hmass g f
      _ = 3 * cgg ^ 2 * cff + 12 * cgg * cfg ^ 2 := by
            simp [cfg, GaussianField.covariance, real_inner_comm]
      _ = 3 * cff * cgg ^ 2 + 12 * cgg * cfg ^ 2 := by ring
  have h33 :
      ∫ ω : Configuration TestFun2D, (ω f) ^ 3 * (ω g) ^ 3 ∂(measure T) =
        9 * cff * cgg * cfg + 6 * cfg ^ 3 := by
    simpa [T, cff, cgg, cfg] using mixed_sixth_moment_three_three mass hmass f g
  have hdrop0 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 0 i) =
        (![f, f, g, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop1 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 1 i) =
        (![f, f, g, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop2 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 2 i) =
        (![f, f, g, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop3 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 3 i) =
        (![f, f, f, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop4 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 4 i) =
        (![f, f, f, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop5 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 5 i) =
        (![f, f, f, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hdrop6 (i : Fin 6) :
      (![f, f, f, g, g, g, g] : Fin 7 → TestFun2D) (Fin.succAbove 6 i) =
        (![f, f, f, g, g, g] : Fin 6 → TestFun2D) i := by
    fin_cases i <;> rfl
  have hprod_ffgggg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 6, ω ((![f, f, g, g, g, g] : Fin 6 → TestFun2D) i) =
        (ω f) ^ 2 * (ω g) ^ 4 := by
    intro ω
    simp [Fin.prod_univ_six]
    ring
  have hprod_fffggg :
      ∀ ω : FieldConfig2D, ∏ i : Fin 6, ω ((![f, f, f, g, g, g] : Fin 6 → TestFun2D) i) =
        (ω f) ^ 3 * (ω g) ^ 3 := by
    intro ω
    simp [Fin.prod_univ_six]
    ring
  simp_rw [hdrop0, hdrop1, hdrop2, hdrop3, hdrop4, hdrop5, hdrop6]
  simp_rw [hprod_ffgggg, hprod_fffggg]
  simp [GaussianField.covariance, cff, cgg, cfg, h24, h33]
  ring

/-- Exact second moment of the quartic fixed-variance re-Wick difference.

This is the sharp Gaussian input for the nonlinear `A`-term in the quartic shell
estimate. The quadratic coefficient is `108`, not `126`, because the constant
`3 c^2` term cancels in the difference before squaring. -/
theorem wickMonomial_four_diff_sq_expectation
    (mass : ℝ) (hmass : 0 < mass) (f g : TestFun2D) (c : ℝ) :
    ∫ ω : FieldConfig2D,
      (wickMonomial 4 c (ω g) - wickMonomial 4 c (ω f)) ^ 2 ∂(freeFieldMeasure mass hmass) =
      105 * (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 4
        - 180 * c * (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 3
        + 108 * c ^ 2 * (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 2
        + 105 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 4
        - 180 * c * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 3
        + 108 * c ^ 2 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2
        - 18 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 *
            (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 2
        - 144 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
            GaussianField.covariance (freeCovarianceCLM mass hmass) g g *
            (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2
        - 48 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 4
        + 36 * c * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
            (GaussianField.covariance (freeCovarianceCLM mass hmass) g g) ^ 2
        + 36 * c * (GaussianField.covariance (freeCovarianceCLM mass hmass) f f) ^ 2 *
            GaussianField.covariance (freeCovarianceCLM mass hmass) g g
        + 144 * c * GaussianField.covariance (freeCovarianceCLM mass hmass) g g *
            (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2
        + 144 * c * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
            (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2
        - 72 * c ^ 2 * GaussianField.covariance (freeCovarianceCLM mass hmass) f f *
            GaussianField.covariance (freeCovarianceCLM mass hmass) g g
        - 144 * c ^ 2 * (GaussianField.covariance (freeCovarianceCLM mass hmass) f g) ^ 2 := by
  let T := freeCovarianceCLM mass hmass
  let cff := GaussianField.covariance T f f
  let cgg := GaussianField.covariance T g g
  let cfg := GaussianField.covariance T f g
  have h4f :
      ∫ ω : FieldConfig2D, (ω f) ^ 4 ∂(freeFieldMeasure mass hmass) = 3 * cff ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion mass hmass f 2]
    have h2f :
        ∫ ω : FieldConfig2D, (ω f) ^ 2 ∂(freeFieldMeasure mass hmass) = cff := by
      have hcross : ∫ ω : Configuration TestFun2D, ω f * ω f ∂(measure T) = cff := by
        simpa [GaussianField.covariance, cff] using cross_moment_eq_covariance T f f
      simpa [pow_two, T] using hcross
    rw [h2f]
    ring
  have h4g :
      ∫ ω : FieldConfig2D, (ω g) ^ 4 ∂(freeFieldMeasure mass hmass) = 3 * cgg ^ 2 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, moment_recursion mass hmass g 2]
    have h2g :
        ∫ ω : FieldConfig2D, (ω g) ^ 2 ∂(freeFieldMeasure mass hmass) = cgg := by
      have hcross : ∫ ω : Configuration TestFun2D, ω g * ω g ∂(measure T) = cgg := by
        simpa [GaussianField.covariance, cgg] using cross_moment_eq_covariance T g g
      simpa [pow_two, T] using hcross
    rw [h2g]
    ring
  have h6f :
      ∫ ω : FieldConfig2D, (ω f) ^ 6 ∂(freeFieldMeasure mass hmass) = 15 * cff ^ 3 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion mass hmass f 4, h4f]
    ring
  have h6g :
      ∫ ω : FieldConfig2D, (ω g) ^ 6 ∂(freeFieldMeasure mass hmass) = 15 * cgg ^ 3 := by
    rw [show (6 : ℕ) = 4 + 2 from rfl, moment_recursion mass hmass g 4, h4g]
    ring
  have h8f :
      ∫ ω : FieldConfig2D, (ω f) ^ 8 ∂(freeFieldMeasure mass hmass) = 105 * cff ^ 4 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion mass hmass f 6, h6f]
    ring
  have h8g :
      ∫ ω : FieldConfig2D, (ω g) ^ 8 ∂(freeFieldMeasure mass hmass) = 105 * cgg ^ 4 := by
    rw [show (8 : ℕ) = 6 + 2 from rfl, moment_recursion mass hmass g 6, h6g]
    ring
  have h22 :
      ∫ ω : FieldConfig2D, (ω f) ^ 2 * (ω g) ^ 2 ∂(freeFieldMeasure mass hmass) =
        cff * cgg + 2 * cfg ^ 2 := by
    simpa [T, cff, cgg, cfg] using mixed_fourth_moment_two_two mass hmass f g
  have h42 :
      ∫ ω : FieldConfig2D, (ω f) ^ 4 * (ω g) ^ 2 ∂(freeFieldMeasure mass hmass) =
        3 * cff ^ 2 * cgg + 12 * cff * cfg ^ 2 := by
    simpa [T, cff, cgg, cfg] using mixed_sixth_moment_four_two mass hmass f g
  have h24 :
      ∫ ω : FieldConfig2D, (ω f) ^ 2 * (ω g) ^ 4 ∂(freeFieldMeasure mass hmass) =
        3 * cff * cgg ^ 2 + 12 * cgg * cfg ^ 2 := by
    calc
      ∫ ω : FieldConfig2D, (ω f) ^ 2 * (ω g) ^ 4 ∂(freeFieldMeasure mass hmass)
          = ∫ ω : FieldConfig2D, (ω g) ^ 4 * (ω f) ^ 2 ∂(freeFieldMeasure mass hmass) := by
              congr with ω
              ring
      _ = 3 * cgg ^ 2 * cff + 12 * cgg * (GaussianField.covariance T g f) ^ 2 := by
            simpa [T, cff, cgg, mul_comm, mul_left_comm, mul_assoc] using
              mixed_sixth_moment_four_two mass hmass g f
      _ = 3 * cff * cgg ^ 2 + 12 * cgg * cfg ^ 2 := by
            simp [cfg, GaussianField.covariance, real_inner_comm]
            ring
  have h44 :
      ∫ ω : FieldConfig2D, (ω f) ^ 4 * (ω g) ^ 4 ∂(freeFieldMeasure mass hmass) =
        9 * cff ^ 2 * cgg ^ 2 + 72 * cff * cgg * cfg ^ 2 + 24 * cfg ^ 4 := by
    simpa [T, cff, cgg, cfg] using mixed_eighth_moment_four_four mass hmass f g
  have hexpand :
      (fun ω : FieldConfig2D =>
        (wickMonomial 4 c (ω g) - wickMonomial 4 c (ω f)) ^ 2) =
      (fun ω : FieldConfig2D =>
        (ω g) ^ 8 - 12 * c * (ω g) ^ 6 + 36 * c ^ 2 * (ω g) ^ 4 +
        (ω f) ^ 8 - 12 * c * (ω f) ^ 6 + 36 * c ^ 2 * (ω f) ^ 4 -
        2 * ((ω f) ^ 4 * (ω g) ^ 4) + 12 * c * ((ω f) ^ 4 * (ω g) ^ 2) +
        12 * c * ((ω f) ^ 2 * (ω g) ^ 4) - 72 * c ^ 2 * ((ω f) ^ 2 * (ω g) ^ 2)) := by
    ext ω
    simp [wickMonomial_four]
    ring
  let μ := freeFieldMeasure mass hmass
  have hi8g : Integrable (fun ω : FieldConfig2D => (ω g) ^ 8) μ := power_integrable mass hmass g 8
  have hi6g : Integrable (fun ω : FieldConfig2D => (ω g) ^ 6) μ := power_integrable mass hmass g 6
  have hi4g : Integrable (fun ω : FieldConfig2D => (ω g) ^ 4) μ := power_integrable mass hmass g 4
  have hi8f : Integrable (fun ω : FieldConfig2D => (ω f) ^ 8) μ := power_integrable mass hmass f 8
  have hi6f : Integrable (fun ω : FieldConfig2D => (ω f) ^ 6) μ := power_integrable mass hmass f 6
  have hi4f : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4) μ := power_integrable mass hmass f 4
  have hi44 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4 * (ω g) ^ 4) μ := by
    have hrew :
        (fun ω : FieldConfig2D => (ω f) ^ 4 * (ω g) ^ 4) =
        (fun ω : Configuration TestFun2D =>
          ∏ i : Fin 8, ω ((![f, f, f, f, g, g, g, g] : Fin 8 → TestFun2D) i)) := by
      funext ω
      simp [Fin.prod_univ_eight]
      ring
    rw [hrew]
    exact product_integrable (freeCovarianceCLM mass hmass) 8
      (fun i => (![f, f, f, f, g, g, g, g] : Fin 8 → TestFun2D) i)
  have hi42 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 4 * (ω g) ^ 2) μ := by
    have hrew :
        (fun ω : FieldConfig2D => (ω f) ^ 4 * (ω g) ^ 2) =
        (fun ω : Configuration TestFun2D =>
          ∏ i : Fin 6, ω ((![f, f, f, f, g, g] : Fin 6 → TestFun2D) i)) := by
      funext ω
      simp [Fin.prod_univ_six]
      ring
    rw [hrew]
    exact product_integrable (freeCovarianceCLM mass hmass) 6
      (fun i => (![f, f, f, f, g, g] : Fin 6 → TestFun2D) i)
  have hi24 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2 * (ω g) ^ 4) μ := by
    have hrew :
        (fun ω : FieldConfig2D => (ω f) ^ 2 * (ω g) ^ 4) =
        (fun ω : Configuration TestFun2D =>
          ∏ i : Fin 6, ω ((![f, f, g, g, g, g] : Fin 6 → TestFun2D) i)) := by
      funext ω
      simp [Fin.prod_univ_six]
      ring
    rw [hrew]
    exact product_integrable (freeCovarianceCLM mass hmass) 6
      (fun i => (![f, f, g, g, g, g] : Fin 6 → TestFun2D) i)
  have hi22 : Integrable (fun ω : FieldConfig2D => (ω f) ^ 2 * (ω g) ^ 2) μ := by
    have hrew :
        (fun ω : FieldConfig2D => (ω f) ^ 2 * (ω g) ^ 2) =
        (fun ω : Configuration TestFun2D =>
          ∏ i : Fin 4, ω ((![f, f, g, g] : Fin 4 → TestFun2D) i)) := by
      funext ω
      simp [Fin.prod_univ_four]
      ring
    rw [hrew]
    exact product_integrable (freeCovarianceCLM mass hmass) 4
      (fun i => (![f, f, g, g] : Fin 4 → TestFun2D) i)
  let G8 : FieldConfig2D → ℝ := fun ω => (ω g) ^ 8
  let G6 : FieldConfig2D → ℝ := fun ω => -12 * c * (ω g) ^ 6
  let G4 : FieldConfig2D → ℝ := fun ω => 36 * c ^ 2 * (ω g) ^ 4
  let F8 : FieldConfig2D → ℝ := fun ω => (ω f) ^ 8
  let F6 : FieldConfig2D → ℝ := fun ω => -12 * c * (ω f) ^ 6
  let F4 : FieldConfig2D → ℝ := fun ω => 36 * c ^ 2 * (ω f) ^ 4
  let M44 : FieldConfig2D → ℝ := fun ω => -2 * ((ω f) ^ 4 * (ω g) ^ 4)
  let M42 : FieldConfig2D → ℝ := fun ω => 12 * c * ((ω f) ^ 4 * (ω g) ^ 2)
  let M24 : FieldConfig2D → ℝ := fun ω => 12 * c * ((ω f) ^ 2 * (ω g) ^ 4)
  let M22 : FieldConfig2D → ℝ := fun ω => -72 * c ^ 2 * ((ω f) ^ 2 * (ω g) ^ 2)
  have hsum :
      (fun ω : FieldConfig2D =>
        (ω g) ^ 8 - 12 * c * (ω g) ^ 6 + 36 * c ^ 2 * (ω g) ^ 4 +
        (ω f) ^ 8 - 12 * c * (ω f) ^ 6 + 36 * c ^ 2 * (ω f) ^ 4 -
        2 * ((ω f) ^ 4 * (ω g) ^ 4) + 12 * c * ((ω f) ^ 4 * (ω g) ^ 2) +
        12 * c * ((ω f) ^ 2 * (ω g) ^ 4) - 72 * c ^ 2 * ((ω f) ^ 2 * (ω g) ^ 2)) =
      fun ω => G8 ω + (G6 ω + (G4 ω + (F8 ω + (F6 ω + (F4 ω + (M44 ω + (M42 ω + (M24 ω + M22 ω)))))))) := by
    funext ω
    simp [G8, G6, G4, F8, F6, F4, M44, M42, M24, M22]
    ring
  let T22 : FieldConfig2D → ℝ := fun ω => M24 ω + M22 ω
  let T42 : FieldConfig2D → ℝ := fun ω => M42 ω + T22 ω
  let T44 : FieldConfig2D → ℝ := fun ω => M44 ω + T42 ω
  let TF4 : FieldConfig2D → ℝ := fun ω => F4 ω + T44 ω
  let TF6 : FieldConfig2D → ℝ := fun ω => F6 ω + TF4 ω
  let TF8 : FieldConfig2D → ℝ := fun ω => F8 ω + TF6 ω
  let TG4 : FieldConfig2D → ℝ := fun ω => G4 ω + TF8 ω
  let TG6 : FieldConfig2D → ℝ := fun ω => G6 ω + TG4 ω
  have htail22 : Integrable T22 μ := (hi24.const_mul _).add (hi22.const_mul _)
  have htail42 : Integrable T42 μ := (hi42.const_mul _).add htail22
  have htail44 : Integrable T44 μ := (hi44.const_mul _).add htail42
  have htailF4 : Integrable TF4 μ := (hi4f.const_mul _).add htail44
  have htailF6 : Integrable TF6 μ := (hi6f.const_mul _).add htailF4
  have htailF8 : Integrable TF8 μ := hi8f.add htailF6
  have htailG4 : Integrable TG4 μ := (hi4g.const_mul _).add htailF8
  have htailG6 : Integrable TG6 μ := (hi6g.const_mul _).add htailG4
  have s1 :
      ∫ ω, G8 ω + TG6 ω ∂μ = ∫ ω, G8 ω ∂μ + ∫ ω, TG6 ω ∂μ := by
    exact integral_add hi8g htailG6
  have s2 :
      ∫ ω, G6 ω + TG4 ω ∂μ = ∫ ω, G6 ω ∂μ + ∫ ω, TG4 ω ∂μ := by
    exact integral_add (hi6g.const_mul _) htailG4
  have s3 :
      ∫ ω, G4 ω + TF8 ω ∂μ = ∫ ω, G4 ω ∂μ + ∫ ω, TF8 ω ∂μ := by
    exact integral_add (hi4g.const_mul _) htailF8
  have s4 :
      ∫ ω, F8 ω + TF6 ω ∂μ = ∫ ω, F8 ω ∂μ + ∫ ω, TF6 ω ∂μ := by
    exact integral_add hi8f htailF6
  have s5 :
      ∫ ω, F6 ω + TF4 ω ∂μ = ∫ ω, F6 ω ∂μ + ∫ ω, TF4 ω ∂μ := by
    exact integral_add (hi6f.const_mul _) htailF4
  have s6 :
      ∫ ω, F4 ω + T44 ω ∂μ = ∫ ω, F4 ω ∂μ + ∫ ω, T44 ω ∂μ := by
    exact integral_add (hi4f.const_mul _) htail44
  have s7 :
      ∫ ω, M44 ω + T42 ω ∂μ = ∫ ω, M44 ω ∂μ + ∫ ω, T42 ω ∂μ := by
    exact integral_add (hi44.const_mul _) htail42
  have s8 :
      ∫ ω, M42 ω + T22 ω ∂μ = ∫ ω, M42 ω ∂μ + ∫ ω, T22 ω ∂μ := by
    exact integral_add (hi42.const_mul _) htail22
  have s9 :
      ∫ ω, T22 ω ∂μ = ∫ ω, M24 ω ∂μ + ∫ ω, M22 ω ∂μ := by
    exact integral_add (hi24.const_mul _) (hi22.const_mul _)
  have hTG6 : (fun ω => G8 ω + TG6 ω) =
      (fun ω => G8 ω + (G6 ω + (G4 ω + (F8 ω + (F6 ω + (F4 ω + (M44 ω + (M42 ω + (M24 ω + M22 ω))))))))) := by
    funext ω
    simp [TG6, TG4, TF8, TF6, TF4, T44, T42, T22]
  have hM44 :
      (-2 : ℝ) * (∫ ω, ω f ^ 4 * ω g ^ 4 ∂μ) =
        -2 * (9 * cff ^ 2 * cgg ^ 2 + 72 * cff * cgg * cfg ^ 2 + 24 * cfg ^ 4) := by
    rw [h44]
  have hM42 :
      12 * c * (∫ ω, ω f ^ 4 * ω g ^ 2 ∂μ) =
        12 * c * (3 * cff ^ 2 * cgg + 12 * cff * cfg ^ 2) := by
    rw [h42]
  have hM24 :
      12 * c * (∫ ω, ω f ^ 2 * ω g ^ 4 ∂μ) =
        12 * c * (3 * cff * cgg ^ 2 + 12 * cgg * cfg ^ 2) := by
    rw [h24]
  have hM22' :
      ∫ ω, M22 ω ∂μ = -72 * c ^ 2 * (cff * cgg + 2 * cfg ^ 2) := by
    change ∫ ω, (-72 * c ^ 2) * (ω f ^ 2 * ω g ^ 2) ∂μ =
      -72 * c ^ 2 * (cff * cgg + 2 * cfg ^ 2)
    rw [integral_const_mul, h22]
  rw [hexpand, hsum, ← hTG6, s1, s2, s3, s4, s5, s6, s7, s8, s9,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul, integral_const_mul,
    integral_const_mul]
  rw [h8g, h6g, h4g, h8f, h6f, h4f, hM24, hM22', hM42, hM44]
  simp only [T, cff, cgg, cfg]
  ring_nf

/-- Exact decomposition of the quartic Wick-power increment between two UV
    cutoffs. This separates the increment into:
    1. a field-increment term at fixed variance, and
    2. a covariance-renormalization correction via re-Wick ordering.

    This is the algebraic entry point for shellwise `L²` estimates. -/
theorem wickPower_four_step_decomposition
    (mass : ℝ) (κ₁ κ₂ : UVCutoff) (ω : FieldConfig2D) (x : Spacetime2D) :
    wickPower 4 mass κ₂ ω x - wickPower 4 mass κ₁ ω x =
      (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
        ((rawFieldEval mass κ₂ ω x) ^ 3 +
         (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
         rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
         (rawFieldEval mass κ₁ ω x) ^ 3 -
         6 * regularizedPointCovariance mass κ₁ *
           (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x))
      - 6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
          wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x)
      + 3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 := by
  rw [wickPower, wickMonomial_rewick_four]
  have hdiff := wickMonomial_four_diff_factor
      (regularizedPointCovariance mass κ₁)
      (rawFieldEval mass κ₂ ω x)
      (rawFieldEval mass κ₁ ω x)
  calc
    wickMonomial 4 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x) -
        6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
          wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x) +
        3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 -
      wickMonomial 4 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₁ ω x)
        = (wickMonomial 4 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x) -
            wickMonomial 4 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₁ ω x)) -
            6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
              wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x) +
            3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 := by
          ring
    _ = (rawFieldEval mass κ₂ ω x - rawFieldEval mass κ₁ ω x) *
          ((rawFieldEval mass κ₂ ω x) ^ 3 +
           (rawFieldEval mass κ₂ ω x) ^ 2 * rawFieldEval mass κ₁ ω x +
           rawFieldEval mass κ₂ ω x * (rawFieldEval mass κ₁ ω x) ^ 2 +
           (rawFieldEval mass κ₁ ω x) ^ 3 -
           6 * regularizedPointCovariance mass κ₁ *
             (rawFieldEval mass κ₂ ω x + rawFieldEval mass κ₁ ω x)) -
          6 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) *
            wickMonomial 2 (regularizedPointCovariance mass κ₁) (rawFieldEval mass κ₂ ω x) +
          3 * (regularizedPointCovariance mass κ₂ - regularizedPointCovariance mass κ₁) ^ 2 := by
          rw [hdiff]

/-- **Wick monomials are bounded by a polynomial in |x| of the same degree.**
    For any variance parameter c and degree n, there exists C > 0 such that
      |wickMonomial n c x| ≤ C * (1 + |x|)ⁿ  for all x.
    This is the key algebraic bound underlying the re-Wick-ordering estimates. -/
theorem wickMonomial_bound : ∀ (n : ℕ) (c : ℝ),
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |wickMonomial n c x| ≤ C * (1 + |x|) ^ n
  | 0, c => ⟨1, one_pos, fun x => by simp⟩
  | 1, c => ⟨1, one_pos, fun x => by
    simp only [wickMonomial_one, pow_one, one_mul]
    linarith [abs_nonneg x]⟩
  | n + 2, c => by
    obtain ⟨C₁, hC₁pos, hC₁⟩ := wickMonomial_bound (n + 1) c
    obtain ⟨C₂, hC₂pos, hC₂⟩ := wickMonomial_bound n c
    refine ⟨C₁ + (↑n + 1) * |c| * C₂, by positivity, fun x => ?_⟩
    simp only [wickMonomial_succ_succ]
    have h1 := hC₁ x
    have h2 := hC₂ x
    have hge1 : 1 ≤ 1 + |x| := le_add_of_nonneg_right (abs_nonneg x)
    -- Set up abbreviations for the two terms
    set a := x * wickMonomial (n + 1) c x with ha_def
    set b := (↑n + 1) * c * wickMonomial n c x with hb_def
    -- Triangle inequality |a - b| ≤ |a| + |b| via norm_add_le
    have htri : |a - b| ≤ |a| + |b| := by
      have h := norm_add_le a (-b)
      simp only [Real.norm_eq_abs, abs_neg, ← sub_eq_add_neg] at h
      exact h
    -- Bound |a| using IH
    have ha_bound : |a| ≤ |x| * (C₁ * (1 + |x|) ^ (n + 1)) := by
      simp only [ha_def, abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg x)
    -- Bound |b| using IH
    have hb_bound : |b| ≤ (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ n) := by
      simp only [hb_def, abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ ↑n + 1 by positivity)]
      exact mul_le_mul_of_nonneg_left h2 (by positivity)
    -- Main bound via calc
    calc |a - b|
        ≤ |a| + |b| := htri
      _ ≤ |x| * (C₁ * (1 + |x|) ^ (n + 1))
          + (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ n) := add_le_add ha_bound hb_bound
      _ ≤ (1 + |x|) * (C₁ * (1 + |x|) ^ (n + 1))
          + (↑n + 1) * |c| * (C₂ * (1 + |x|) ^ (n + 2)) := by
          apply add_le_add
          · exact mul_le_mul_of_nonneg_right (by linarith [abs_nonneg x]) (by positivity)
          · exact mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (pow_le_pow_right₀ hge1 (Nat.le_add_right n 2)) hC₂pos.le)
              (by positivity)
      _ = (C₁ + (↑n + 1) * |c| * C₂) * (1 + |x|) ^ (n + 2) := by ring

end
