/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Regularity
import OSReconstruction.Wightman.Reconstruction

/-!
# OS Axioms for φ⁴₂

This file packages OS-style consequences from currently available Schwinger and
regularity inputs. It should not be read as a fully local proof that the φ⁴₂
construction has already established OS0-OS4 from first principles inside this
repository.

The hard mathematical content is still open through explicit theorem hypotheses
and frontier theorems. This file assembles those inputs into the
`OsterwalderSchraderAxioms` API used downstream.

The four axioms are:
- **OS0 (Temperedness)**: S_n are tempered distributions on S(ℝ^{2n})
- **OS1 (Regularity)**: |S{f}| ≤ exp(c · N'(f)) (linear growth)
- **OS2 (Euclidean covariance)**: S_n invariant under translations and SO(2) rotations
- **OS3 (Reflection positivity)**: RP inner product is positive semidefinite

## References

* [Glimm-Jaffe] Theorem 12.1.1, Chapter 12
* [Osterwalder-Schrader I, II]
-/

noncomputable section

open MeasureTheory Reconstruction

/-! ## Packaged Schwinger input -/

/-- Canonical packaged Schwinger functions used by the OS interfaces. -/
class SchwingerFunctionModel (params : Phi4Params) where
  schwingerFunctions : SchwingerFunctions 1

/-- Honest theorem-level frontier: measure-level reflection positivity for
    linear observables against `infiniteVolumeMeasure`. -/
theorem gap_measure_os3_reflection_positive (params : Phi4Params)
    [InfiniteVolumeMeasureModel params]
    (n : ℕ) (f : Fin n → TestFun2D) (c : Fin n → ℂ)
    (hsupp : ∀ i, supportedInPositiveTime (f i)) :
    0 ≤ (∑ i, ∑ j, c i * starRingEnd ℂ (c j) *
      ∫ ω, ω (testFunTimeReflect (f i)) * ω (f j)
        ∂(infiniteVolumeMeasure params)).re := by
  sorry

/-! ## Schwinger functions as distributions

The infinite volume Schwinger functions define tempered distributions on S(ℝ^{2n}). -/

/-- The φ⁴₂ Schwinger functions packaged as a `SchwingerFunctions` (from OSreconstruction).
    Here d = 1 because OSreconstruction uses spacetime dimension d+1, and we have d+1 = 2.

    S_n : S(ℝ^{n×2}) → ℂ is defined by:
      S_n(f) = ∫ φ(x₁)⋯φ(xₙ) f(x₁,...,xₙ) dx₁⋯dxₙ dμ(φ)

    In the current branch this is a packaging layer over
    `SchwingerFunctionModel`, not yet a direct local construction from the
    infinite-volume measure. -/
def phi4SchwingerFunctions (params : Phi4Params)
    [SchwingerFunctionModel params] :
    SchwingerFunctions 1 :=
  SchwingerFunctionModel.schwingerFunctions (params := params)

/-! ## Main theorem: OS axioms hold -/

/-- Assembly theorem: if the explicit OS interfaces are provided and weak
    coupling is available, the packaged Schwinger functions satisfy OS0-OS4.

    The remaining OS0/OS2/E2/E3 obligations are still explicit hypotheses here;
    they have not yet all been surfaced as local named frontier theorems. -/
theorem phi4_satisfies_OS (params : Phi4Params)
    [SchwingerFunctionModel params]
    (hos0 : ∀ n, Continuous (phi4SchwingerFunctions params n))
    (hos2_translation :
      ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g)
    (hos2_rotation :
      ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
        R.transpose * R = 1 → R.det = 1 →
        ∀ (f g : SchwartzNPoint 1 n),
          (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
          phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g)
    (he2 :
      ∀ (F : BorchersSequence 1),
        (∀ n, ∀ x : NPointDomain 1 n,
          (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
        (OSInnerProduct 1 (phi4SchwingerFunctions params) F F).re ≥ 0)
    (he3_symmetric :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g)
    (threshold : ℝ)
    (hcluster :
      params.coupling < threshold →
        ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
          ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
              ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
              ∀ (g_a : SchwartzNPoint 1 m),
                (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
                ‖phi4SchwingerFunctions params (n + m) (f.tensorProduct g_a) -
                  phi4SchwingerFunctions params n f *
                    phi4SchwingerFunctions params m g‖ < ε)
    (hsmall : params.coupling < threshold) :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params := by
  refine ⟨{
    S := phi4SchwingerFunctions params
    E0_tempered := hos0
    E1_translation_invariant := hos2_translation
    E1_rotation_invariant := hos2_rotation
    E2_reflection_positive := he2
    E3_symmetric := he3_symmetric
    E4_cluster := by
      simpa using hcluster hsmall
  }, rfl⟩

end
