import Mathlib.MeasureTheory.SpecificCodomains.WithLp
import Mathlib.Probability.Distributions.Gaussian.CharFun
import Mathlib.Probability.Moments.CovarianceBilin

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

/-!
# Finite-Dimensional Euclidean Gaussian Infrastructure

This file collects finite-dimensional Gaussian lemmas on
`EuclideanSpace ℝ ι` and the corresponding raw coordinate space `ι → ℝ`.
These are used to reduce finite-dimensional centered Gaussian arguments
in `Phi4.WickProduct` to standard product Gaussian calculations.
-/

namespace Phi4

/-- The standard product Gaussian on the raw coordinate space `ι → ℝ`. -/
abbrev standardGaussianRaw (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

/-- The standard Gaussian on `EuclideanSpace ℝ ι`, obtained by pushing forward
the product Gaussian on coordinates along the canonical Euclidean equivalence. -/
abbrev standardGaussianEuclidean (ι : Type*) [Fintype ι] :
    Measure (EuclideanSpace ℝ ι) :=
  (standardGaussianRaw ι).map (EuclideanSpace.equiv ι ℝ).symm

/-- Coordinate covariances of the standard product Gaussian on a finite real
coordinate space are Kronecker deltas. -/
theorem standardGaussian_coordinate_cov
    {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[(fun x : ι → ℝ => x i), (fun x => x j); standardGaussianRaw ι] =
      if i = j then 1 else 0 := by
  have hX : ∀ k : ι, MemLp (fun ω : ι → ℝ => ω k) 2 (standardGaussianRaw ι) := by
    intro k
    simpa [standardGaussianRaw, Function.comp] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
        (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k)
  by_cases hij : i = j
  · subst hij
    rw [covariance_self (hX i).aemeasurable, ← variance_id_map]
    · rw [(measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).map_eq]
      simp
    · simpa using
        (((measurePreserving_eval (fun _ : ι => gaussianReal 0 1) i).measurable :
          Measurable (fun ω : ι → ℝ => ω i)).aemeasurable)
  · have hi : iIndepFun (fun k (ω : ι → ℝ) => ω k) (standardGaussianRaw ι) := by
      exact iIndepFun_pi (fun k => measurable_id.aemeasurable)
    simpa [standardGaussianRaw, hij] using
      (hi.indepFun hij).covariance_eq_zero (hX i) (hX j)

/-- The standard Gaussian on finite Euclidean space has covariance bilinear form
equal to the ambient inner product. -/
theorem standardGaussian_covarianceBilin_euclidean_id
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x y : EuclideanSpace ℝ ι) :
    ProbabilityTheory.covarianceBilin (standardGaussianEuclidean ι) x y = inner ℝ x y := by
  have hX : ∀ k : ι, MemLp (fun ω : ι → ℝ => ω k) 2 (standardGaussianRaw ι) := by
    intro k
    simpa [standardGaussianRaw, Function.comp] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
        (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k)
  rw [show standardGaussianEuclidean ι =
      (standardGaussianRaw ι).map (fun ω ↦ WithLp.toLp 2 (fun k => ω k)) by rfl]
  rw [ProbabilityTheory.covarianceBilin_apply_pi hX x y]
  have hcov : ∀ i j : ι,
      cov[(fun x : ι → ℝ => x i), (fun x => x j); standardGaussianRaw ι] = if i = j then 1 else 0 := by
    intro i j
    simpa using standardGaussian_coordinate_cov (ι := ι) i j
  simp_rw [hcov]
  have hsum : ∑ i, ∑ j, x i * y j * (if i = j then 1 else 0) = ∑ i, x i * y i := by
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine (Finset.sum_eq_single i ?_ ?_).trans ?_
    · intro j hj hji
      have hij : i ≠ j := fun h => hji h.symm
      simp [hij]
    · intro hi_not_mem
      simp at hi_not_mem
    · simp
  rw [hsum, PiLp.inner_apply]
  simp [RCLike.inner_apply, mul_comm]

/-- Covariance bilinear form of a linear image of the finite-dimensional
standard Gaussian. -/
theorem covarianceBilin_map_standardGaussianEuclidean
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ]
    (L : EuclideanSpace ℝ ι →L[ℝ] EuclideanSpace ℝ κ)
    (x y : EuclideanSpace ℝ κ) :
    ProbabilityTheory.covarianceBilin ((standardGaussianEuclidean ι).map L) x y =
      inner ℝ (L.adjoint x) (L.adjoint y) := by
  have hX : ∀ k : ι, MemLp (fun ω : ι → ℝ => ω k) 2 (standardGaussianRaw ι) := by
    intro k
    simpa [standardGaussianRaw, Function.comp] using
      (memLp_id_gaussianReal' (μ := 0) (v := 1) 2 (by norm_num)).comp_measurePreserving
        (measurePreserving_eval (fun _ : ι => gaussianReal 0 1) k)
  have hmem : MemLp (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) 2
      (standardGaussianEuclidean ι) := by
    rw [show standardGaussianEuclidean ι =
        (standardGaussianRaw ι).map (fun ω ↦ WithLp.toLp 2 (fun k => ω k)) by rfl]
    exact (memLp_map_measure_iff aestronglyMeasurable_id (by fun_prop)).2 (MemLp.of_eval_piLp hX)
  rw [ProbabilityTheory.covarianceBilin_map hmem L x y]
  exact standardGaussian_covarianceBilin_euclidean_id (L.adjoint x) (L.adjoint y)

/-- If a finite-dimensional raw Gaussian has coordinatewise zero mean, then its
pushforward to Euclidean space also has zero mean. -/
theorem centered_mean_zero_map_euclidean
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (μ : Measure (ι → ℝ)) [IsGaussian μ]
    (hμ : ∀ i : ι, ∫ x, x i ∂μ = 0) :
    ((μ.map (EuclideanSpace.equiv ι ℝ).symm))[id] = 0 := by
  let μe : Measure (EuclideanSpace ℝ ι) := μ.map (EuclideanSpace.equiv ι ℝ).symm
  have hI : Integrable (id : EuclideanSpace ℝ ι → EuclideanSpace ℝ ι) μe := by
    dsimp [μe]
    simpa using (ProbabilityTheory.IsGaussian.integrable_id (μ := μe))
  ext i
  rw [MeasureTheory.eval_integral_piLp (q := 2) (E := fun _ : ι => ℝ)
    (μ := μe) (f := id) (fun j => hI.eval_piLp j) i]
  rw [show μe = μ.map (EuclideanSpace.equiv ι ℝ).symm by rfl, integral_map]
  · simpa using hμ i
  · fun_prop
  · exact (PiLp.continuous_apply (p := 2) (β := fun _ : ι => ℝ) i).aestronglyMeasurable

end Phi4
