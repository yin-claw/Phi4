/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part2

noncomputable section

open MeasureTheory Reconstruction
open scoped ENNReal NNReal

/-! ## Wightman reconstruction -/

/-- Construct Wightman existence from explicit linear-growth and reconstruction
    rule data at fixed `params`. -/
theorem phi4_wightman_exists (params : Phi4Params) :
    [SchwingerFunctionModel params] →
    (hlinear : ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS)) →
    (hreconstruct : ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _ hlinear hreconstruct
  rcases hlinear with ⟨OS, hOS_lg⟩
  rcases hOS_lg with ⟨hS, hlg_nonempty⟩
  rcases hlg_nonempty with ⟨hlg⟩
  rcases hreconstruct OS hlg with ⟨Wfn, hWR⟩
  exact ⟨Wfn, OS, hS, hWR⟩

/-- Direct weak-coupling endpoint from:
    1) interface-level OS package data under weak coupling,
    2) explicit pointwise-in-`f` finite-volume uniform generating-functional bounds,
    3) dense image of product tensors in each positive-order Schwartz `n`-point space,
    4) order-zero normalization (`S₀(g) = g(0)`), using Sobolev index `0`. -/
theorem
    phi4_wightman_exists_of_interfaces_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
    (params : Phi4Params) :
    [SchwingerLimitModel params] →
    [SchwingerFunctionModel params] →
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos)) →
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω))) →
    (hcore :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a D r D2 r2 : ℝ,
          0 < a ∧ 0 ≤ D ∧ 0 ≤ r ∧ Real.exp (q * a) * r < 1 ∧
          0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D * r ^ n) ∧
          (∀ n : ℕ,
            Integrable
              (fun ω : FieldConfig2D =>
                Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
              (freeFieldMeasure params.mass params.mass_pos)) ∧
          (∀ n : ℕ,
            ∫ ω : FieldConfig2D,
              Real.exp ((-(2 * q)) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)
              ∂(freeFieldMeasure params.mass params.mass_pos)
            ≤ D2 * r2 ^ n)) →
    (hos0 : ∀ n, Continuous (phi4SchwingerFunctions params n)) →
    (hos0_linear : ∀ n, IsLinearMap ℂ (phi4SchwingerFunctions params n)) →
    (hos2_translation :
      ∀ (n : ℕ) (a : Fin 2 → ℝ) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x i + a)) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g) →
    (hos2_rotation :
      ∀ (n : ℕ) (R : Matrix (Fin 2) (Fin 2) ℝ),
        R.transpose * R = 1 → R.det = 1 →
        ∀ (f g : SchwartzNPoint 1 n),
          (∀ x, g.toFun x = f.toFun (fun i => R.mulVec (x i))) →
          phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g) →
    (he2 :
      ∀ (F : BorchersSequence 1),
        (∀ n, ∀ x : NPointDomain 1 n,
          (F.funcs n).toFun x ≠ 0 → x ∈ PositiveTimeRegion 1 n) →
        (OSInnerProduct 1 (phi4SchwingerFunctions params) F F).re ≥ 0) →
    (he3_symmetric :
      ∀ (n : ℕ) (σ : Equiv.Perm (Fin n)) (f g : SchwartzNPoint 1 n),
        (∀ x, g.toFun x = f.toFun (fun i => x (σ i))) →
        phi4SchwingerFunctions params n f = phi4SchwingerFunctions params n g) →
    (threshold : ℝ) →
    (hcluster :
      params.coupling < threshold →
        ∀ (n m : ℕ) (f : SchwartzNPoint 1 n) (g : SchwartzNPoint 1 m),
          ∀ ε : ℝ, ε > 0 → ∃ R : ℝ, R > 0 ∧
              ∀ a : SpacetimeDim 1, a 0 = 0 → (∑ i : Fin 1, (a (Fin.succ i))^2) > R^2 →
              ∀ (g_a : SchwartzNPoint 1 m),
                (∀ x : NPointDomain 1 m, g_a x = g (fun i => x i - a)) →
                ‖phi4SchwingerFunctions params (n + m) (f.tensorProduct g_a) -
                  phi4SchwingerFunctions params n f *
                    phi4SchwingerFunctions params m g‖ < ε) →
    (hsmall : params.coupling < threshold) →
    (alpha beta gamma : ℝ) →
    (hbeta : 0 < beta) →
    (huniform : ∀ h : TestFun2D, ∃ c : ℝ, ∀ Λ : Rectangle,
      |generatingFunctional params Λ h| ≤ Real.exp (c * normFunctional h)) →
    (hcompat :
      ∀ (n : ℕ) (f : Fin n → TestFun2D),
        phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f) =
          (infiniteVolumeSchwinger params n f : ℂ)) →
    (hreduce :
      ∀ (c : ℝ) (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D),
        ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) ≤
          alpha * beta ^ n * (n.factorial : ℝ) ^ gamma *
            SchwartzMap.seminorm ℝ 0 0
              (schwartzProductTensorFromTestFamily f)) →
    (hdense :
      ∀ (n : ℕ) (_hn : 0 < n),
        DenseRange (fun f : Fin n → TestFun2D =>
          schwartzProductTensorFromTestFamily f)) →
    (hreconstruct : ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W) →
    ∃ (Wfn : WightmanFunctions 1),
      ∃ (OS : OsterwalderSchraderAxioms 1),
        OS.S = phi4SchwingerFunctions params ∧
        IsWickRotationPair OS.S Wfn.W := by
  intro _hlimit _hsch
    hcutoff_meas hcutoff_ae hcore
    hos0 hos0_linear hos2_translation hos2_rotation he2 he3_symmetric threshold hcluster
    hsmall alpha beta gamma hbeta huniform hcompat hreduce hdense hreconstruct
  rcases
      interactionWeightModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
        (params := params)
        hcutoff_meas hcutoff_ae hcore with ⟨hIntModel⟩
  letI : InteractionWeightModel params := hIntModel
  have hmixed :
      ∀ (n : ℕ) (_hn : 0 < n) (f : Fin n → TestFun2D), ∃ c : ℝ,
        ‖phi4SchwingerFunctions params n (schwartzProductTensorFromTestFamily f)‖ ≤
          ∑ i : Fin n, (Nat.factorial n : ℝ) *
            (Real.exp (c * normFunctional (f i)) +
              Real.exp (c * normFunctional (-(f i)))) := by
    intro n hn f
    exact phi4_productTensor_mixed_bound_of_uniform_generating_bound
      params huniform hcompat n hn f
  have hzero : ∀ f : Fin 0 → TestFun2D, infiniteVolumeSchwinger params 0 f = 1 := by
    intro f
    exact infiniteVolumeSchwinger_zero (params := params) f
  rcases gap_phi4_linear_growth params hos0 hos0_linear hos2_translation hos2_rotation he2
      he3_symmetric threshold hcluster hsmall alpha beta gamma hbeta
      hmixed hcompat hzero hreduce hdense with ⟨OS, hOS, hlg_nonempty⟩
  exact phi4_wightman_exists params
    (hlinear := ⟨OS, hOS, hlg_nonempty⟩)
    (hreconstruct := hreconstruct)


end
