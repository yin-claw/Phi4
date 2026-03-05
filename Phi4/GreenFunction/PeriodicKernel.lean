/- 
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.FreeField

/-!
# Periodic Image-Sum Kernel Infrastructure

This file develops concrete method-of-images infrastructure for periodic
boundary kernels on rectangles/tori:

* periodic lattice shifts `periodicShift` and translated points `shiftPoint`,
* finite index windows `periodicIndexFinset`,
* truncated periodic image sums `periodicKernelTrunc`.

These definitions are mathematically sound and physically motivated:
the periodic Green kernel on a torus is represented by summing free-space
propagators over lattice images.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Phi4

/-- Periodic lattice shift vector with periods `L₁`, `L₂` and indices `(m,n)`. -/
def periodicShift (L₁ L₂ : ℝ) (m n : ℤ) : Spacetime2D :=
  EuclideanSpace.equiv (Fin 2) ℝ |>.symm
    (fun i => if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂)

@[simp] theorem periodicShift_apply (L₁ L₂ : ℝ) (m n : ℤ) (i : Fin 2) :
    periodicShift L₁ L₂ m n i = if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂ := by
  simp [periodicShift]

/-- Translate a spacetime point by a periodic lattice shift. -/
def shiftPoint (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) : Spacetime2D :=
  x + periodicShift L₁ L₂ m n

@[simp] theorem shiftPoint_apply (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) (i : Fin 2) :
    shiftPoint L₁ L₂ m n x i =
      x i + (if i = 0 then (m : ℝ) * L₁ else (n : ℝ) * L₂) := by
  simp [shiftPoint, periodicShift]

@[simp] theorem shiftPoint_zero_zero (L₁ L₂ : ℝ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ 0 0 x = x := by
  ext i
  simp [shiftPoint, periodicShift]

@[simp] theorem shiftPoint_sub (L₁ L₂ : ℝ) (m n : ℤ) (x y : Spacetime2D) :
    shiftPoint L₁ L₂ m n x - shiftPoint L₁ L₂ m n y = x - y := by
  simp [shiftPoint, sub_eq_add_neg, add_assoc, add_comm]

theorem periodicShift_add_indices (L₁ L₂ : ℝ)
    (m₁ m₂ n₁ n₂ : ℤ) :
    periodicShift L₁ L₂ (m₁ + m₂) (n₁ + n₂) =
      periodicShift L₁ L₂ m₁ n₁ + periodicShift L₁ L₂ m₂ n₂ := by
  ext i
  by_cases hi : i = 0
  · simp [periodicShift, hi, add_mul]
  · simp [periodicShift, hi, add_mul]

theorem shiftPoint_add_indices (L₁ L₂ : ℝ)
    (m₁ m₂ n₁ n₂ : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ (m₁ + m₂) (n₁ + n₂) x =
      shiftPoint L₁ L₂ m₁ n₁ (shiftPoint L₁ L₂ m₂ n₂ x) := by
  unfold shiftPoint
  rw [periodicShift_add_indices]
  abel

@[simp] theorem shiftPoint_neg_cancel (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ m n (shiftPoint L₁ L₂ (-m) (-n) x) = x := by
  simpa using (shiftPoint_add_indices L₁ L₂ m (-m) n (-n) x).symm

@[simp] theorem shiftPoint_neg_cancel' (L₁ L₂ : ℝ) (m n : ℤ) (x : Spacetime2D) :
    shiftPoint L₁ L₂ (-m) (-n) (shiftPoint L₁ L₂ m n x) = x := by
  simpa [add_comm] using (shiftPoint_add_indices L₁ L₂ (-m) m (-n) n x).symm

/-- Finite index set `{-N, ..., N}` used in truncated periodic image sums. -/
def periodicIndexFinset (N : ℕ) : Finset ℤ :=
  Finset.Icc (-(N : ℤ)) (N : ℤ)

@[simp] theorem periodicIndexFinset_zero : periodicIndexFinset 0 = ({0} : Finset ℤ) := by
  ext z
  simp [periodicIndexFinset]

/-- One periodic image term in the method-of-images construction. -/
def periodicKernelTerm (mass L₁ L₂ : ℝ) (m n : ℤ)
    (x y : Spacetime2D) : ℝ :=
  freeCovKernel mass x (shiftPoint L₁ L₂ m n y)

/-- Truncated periodic image kernel:
    sum over lattice shifts `(m,n) ∈ {-N,...,N}²`. -/
def periodicKernelTrunc (mass L₁ L₂ : ℝ) (N : ℕ)
    (x y : Spacetime2D) : ℝ :=
  Finset.sum (periodicIndexFinset N) (fun m =>
    Finset.sum (periodicIndexFinset N) (fun n =>
      periodicKernelTerm mass L₁ L₂ m n x y))

@[simp] theorem periodicKernelTrunc_zero (mass L₁ L₂ : ℝ) (x y : Spacetime2D) :
    periodicKernelTrunc mass L₁ L₂ 0 x y = freeCovKernel mass x y := by
  simp [periodicKernelTrunc, periodicKernelTerm]

end Phi4
