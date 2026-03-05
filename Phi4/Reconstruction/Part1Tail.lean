/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Reconstruction.Part1Core

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-- Public linear-growth endpoint from `ReconstructionLinearGrowthModel`. -/
theorem phi4_linear_growth (params : Phi4Params)
    [SchwingerFunctionModel params]
    [ReconstructionLinearGrowthModel params] :
    ∃ OS : OsterwalderSchraderAxioms 1,
      OS.S = phi4SchwingerFunctions params ∧
      Nonempty (OSLinearGrowthCondition 1 OS) := by
  exact ReconstructionLinearGrowthModel.phi4_linear_growth (params := params)

/-- Honest frontier: reconstruction step from OS+linear-growth data via the
    abstract reconstruction backend interface.
    Assumptions are stated explicitly (no interface-class smuggling). -/
theorem gap_phi4_wightman_reconstruction_step (_params : Phi4Params)
    (hreconstruct :
      ∀ (OS : OsterwalderSchraderAxioms 1),
        OSLinearGrowthCondition 1 OS →
          ∃ (Wfn : WightmanFunctions 1),
            IsWickRotationPair OS.S Wfn.W) :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact hreconstruct

/-- Public reconstruction step from OS + linear growth to Wightman data,
    routed through `WightmanReconstructionModel`. -/
theorem phi4_wightman_reconstruction_step (params : Phi4Params)
    [WightmanReconstructionModel params] :
    ∀ (OS : OsterwalderSchraderAxioms 1),
      OSLinearGrowthCondition 1 OS →
        ∃ (Wfn : WightmanFunctions 1),
          IsWickRotationPair OS.S Wfn.W := by
  exact WightmanReconstructionModel.wightman_reconstruction (params := params)
