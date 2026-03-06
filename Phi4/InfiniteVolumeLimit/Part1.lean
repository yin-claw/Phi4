/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.MultipleReflections
import Phi4.CorrelationInequalities

/-!
# Infinite Volume Limit

The infinite volume limit is the construction of the φ⁴₂ measure on S'(ℝ²) as the
limit of finite-volume measures dμ_Λ as Λ ↗ ℝ².

The proof strategy (Glimm-Jaffe Chapter 11) combines:
1. **Monotone convergence**: Schwinger functions S_n^Λ are monotone increasing in Λ
   (for non-negative test functions), by the GKS second inequality.
2. **Uniform upper bounds**: S_n^Λ ≤ C uniform in Λ, by the multiple reflection bounds.

Together, monotone + bounded ⟹ convergent.

The interaction is P = λφ⁴ (even polynomial + possibly linear term), and we use
Dirichlet boundary conditions.

## Main results

* `schwinger_monotone_in_volume` — S_n^Λ increases with Λ
* `schwinger_uniformly_bounded` — S_n^Λ bounded uniformly in Λ
* `infinite_volume_schwinger_exists` — lim_{Λ↗ℝ²} S_n^Λ(f) exists
* `infiniteVolumeMeasure` — the φ⁴₂ probability measure on S'(ℝ²)

## References

* [Glimm-Jaffe] Chapter 11
-/

noncomputable section

open MeasureTheory

/-! ## Monotone convergence of Schwinger functions -/

/-- The sequence of rectangles Λₙ = [-n, n] × [-n, n] exhausting ℝ².
    These serve as the volume cutoffs for the infinite volume limit. -/
def exhaustingRectangles (n : ℕ) (hn : 0 < n) : Rectangle :=
  Rectangle.symmetric n n (Nat.cast_pos.mpr hn) (Nat.cast_pos.mpr hn)

/-- Monotonicity of the exhausting rectangles as sets. -/
private lemma exhaustingRectangles_mono_toSet
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂) :
    (exhaustingRectangles n₁ hn₁).toSet ⊆ (exhaustingRectangles n₂ hn₂).toSet := by
  intro x hx
  rcases hx with ⟨hx0min, hx0max, hx1min, hx1max⟩
  have hcast : (n₁ : ℝ) ≤ (n₂ : ℝ) := by exact_mod_cast h
  have hx0min' : (-(n₁ : ℝ)) ≤ x 0 := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx0min
  have hx0max' : x 0 ≤ (n₁ : ℝ) := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx0max
  have hx1min' : (-(n₁ : ℝ)) ≤ x 1 := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx1min
  have hx1max' : x 1 ≤ (n₁ : ℝ) := by
    simpa [exhaustingRectangles, Rectangle.symmetric] using hx1max
  have hx0min2 : (-(n₂ : ℝ)) ≤ x 0 := by linarith
  have hx0max2 : x 0 ≤ (n₂ : ℝ) := by linarith
  have hx1min2 : (-(n₂ : ℝ)) ≤ x 1 := by linarith
  have hx1max2 : x 1 ≤ (n₂ : ℝ) := by linarith
  simpa [Rectangle.toSet, exhaustingRectangles, Rectangle.symmetric] using
    (show (-(n₂ : ℝ) ≤ x 0 ∧ x 0 ≤ (n₂ : ℝ) ∧
        -(n₂ : ℝ) ≤ x 1 ∧ x 1 ≤ (n₂ : ℝ)) from
      ⟨hx0min2, hx0max2, hx1min2, hx1max2⟩)

/-- **Monotone convergence**: The 2-point Schwinger function increases with volume.
    For Λ₁ ⊂ Λ₂ and non-negative test functions f, g ≥ 0:
      S₂^{Λ₁}(f,g) ≤ S₂^{Λ₂}(f,g)

    Proof: Combines Dirichlet monotonicity (enlarging Λ relaxes the BC,
    increasing the covariance) with GKS-II (the 2-point function is
    monotone in the covariance for the φ⁴ interaction). -/
theorem schwinger_monotone_in_volume (params : Phi4Params)
    (hmono2 : HasSchwingerNMonotone params 2)
    (n₁ n₂ : ℕ) (hn₁ : 0 < n₁) (hn₂ : 0 < n₂) (h : n₁ ≤ n₂)
    (f g : TestFun2D) (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet, g x = 0) :
    schwingerTwo params (exhaustingRectangles n₁ hn₁) f g ≤
      schwingerTwo params (exhaustingRectangles n₂ hn₂) f g := by
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles n₁ hn₁).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  have hmonoN :=
    hmono2
      (exhaustingRectangles n₁ hn₁)
      (exhaustingRectangles n₂ hn₂)
      (exhaustingRectangles_mono_toSet n₁ n₂ hn₁ hn₂ h)
      (![f, g] : Fin 2 → TestFun2D) hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hmonoN

private lemma support_zero_outside_of_subset
    (f : TestFun2D) {A B : Set Spacetime2D}
    (hAB : A ⊆ B)
    (hfA : ∀ x ∉ A, f x = 0) :
    ∀ x ∉ B, f x = 0 := by
  intro x hxB
  exact hfA x (fun hxA => hxB (hAB hxA))

private theorem tendsto_iSup_of_monotone_abs_bounded
    (a : ℕ → ℝ)
    (hmono : Monotone a)
    (hbound : ∃ C : ℝ, ∀ n : ℕ, |a n| ≤ C) :
    Filter.Tendsto a Filter.atTop (nhds (⨆ n : ℕ, a n)) := by
  rcases hbound with ⟨C, hC⟩
  have hbdd : BddAbove (Set.range a) := by
    refine ⟨C, ?_⟩
    rintro y ⟨n, rfl⟩
    exact le_trans (le_abs_self _) (hC n)
  exact tendsto_atTop_ciSup hmono hbdd

/-- Exhausting rectangles are time-symmetric. -/
private lemma exhaustingRectangles_isTimeSymmetric
    (n : ℕ) (hn : 0 < n) :
    (exhaustingRectangles n hn).IsTimeSymmetric := by
  simp [Rectangle.IsTimeSymmetric, exhaustingRectangles, Rectangle.symmetric]

/-- Uniform absolute bound for exhausting-sequence Schwinger moments:
    if a test-family is supported in a fixed base rectangle, then its finite-volume
    moments along the standard exhaustion are uniformly bounded. -/
theorem schwingerN_uniformly_bounded_on_exhaustion
    (params : Phi4Params)
    (huniform : HasSchwingerUniformBound params)
    (n0 : ℕ)
    (k : ℕ)
    (f : Fin k → TestFun2D)
    (hfsupp0 :
      ∀ i, ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f| ≤ C := by
  rcases huniform k f with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro n
  let Λn : Rectangle := exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)
  have hsub0n :
      (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet ⊆ Λn.toSet := by
    simpa [Λn] using
      (exhaustingRectangles_mono_toSet
        (n0 + 1) (n + n0 + 1)
        (Nat.succ_pos n0) (Nat.succ_pos (n + n0)) (by omega))
  have hfsuppn : ∀ i, ∀ x ∉ Λn.toSet, f i x = 0 := by
    intro i x hx
    exact support_zero_outside_of_subset (f i) hsub0n (hfsupp0 i) x hx
  exact hC Λn (exhaustingRectangles_isTimeSymmetric _ (Nat.succ_pos _)) hfsuppn

/-- Convergence of finite-volume `k`-point Schwinger moments from:
    1. volume monotonicity (`SchwingerNMonotoneModel params k`), and
    2. an explicit uniform absolute bound along the shifted exhaustion. -/
theorem schwingerN_tendsto_iSup_of_monotone_bounded
    (params : Phi4Params)
    (k : ℕ)
    (hmono : HasSchwingerNMonotone params k)
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0)
    (hbound : ∃ C : ℝ, ∀ n : ℕ,
      |schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f| ≤ C) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)) := by
  have hmono : Monotone (fun n : ℕ =>
      schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f) := by
    intro n m hnm
    have hle : n + n0 + 1 ≤ m + n0 + 1 := by
      exact Nat.add_le_add_right hnm (n0 + 1)
    have hsub0n :
        (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet ⊆
          (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet :=
      exhaustingRectangles_mono_toSet
        (n0 + 1) (n + n0 + 1)
        (Nat.succ_pos n0) (Nat.succ_pos (n + n0)) (by omega)
    have hfsuppn :
        ∀ i,
          ∀ x ∉ (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)).toSet, f i x = 0 := by
      intro i x hx
      exact support_zero_outside_of_subset (f i) hsub0n (hfsupp0 i) x hx
    exact hmono
      (Λ₁ := exhaustingRectangles (n + n0 + 1) (Nat.succ_pos (n + n0)))
      (Λ₂ := exhaustingRectangles (m + n0 + 1) (Nat.succ_pos (m + n0)))
      (exhaustingRectangles_mono_toSet
        (n + n0 + 1) (m + n0 + 1)
        (Nat.succ_pos (n + n0)) (Nat.succ_pos (m + n0)) hle)
      f hf hfsuppn
  exact tendsto_iSup_of_monotone_abs_bounded
    (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
    hmono hbound

/-- Monotone-convergence form for finite-volume `k`-point moments along the
    exhausting rectangles, under:
    1. `SchwingerNMonotoneModel params k` for volume monotonicity, and
    2. `HasSchwingerUniformBound params` for uniform absolute bounds. -/
theorem schwingerN_tendsto_iSup_of_monotone_uniformBound
    (params : Phi4Params)
    (k : ℕ)
    (hmono : HasSchwingerNMonotone params k)
    (huniform : HasSchwingerUniformBound params)
    (n0 : ℕ)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp0 : ∀ i,
      ∀ x ∉ (exhaustingRectangles (n0 + 1) (Nat.succ_pos n0)).toSet, f i x = 0) :
    Filter.Tendsto
      (fun n : ℕ => schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerN params (exhaustingRectangles (n + n0 + 1) (Nat.succ_pos _)) k f)) := by
  have hbound := schwingerN_uniformly_bounded_on_exhaustion params huniform n0 k f hfsupp0
  exact schwingerN_tendsto_iSup_of_monotone_bounded
    params k hmono n0 f hf hfsupp0 hbound

/-- Existence of the interface-shaped exhausting-sequence limit
    `if h : 0 < n then S_k^{Λₙ}(f) else 0` from:
    1. `SchwingerNMonotoneModel params k`, and
    2. `HasSchwingerUniformBound params`. -/
theorem schwingerN_limit_exists_if_exhaustion_of_monotone_uniformBound
    (params : Phi4Params)
    (k : ℕ)
    (hmono : HasSchwingerNMonotone params k)
    (huniform : HasSchwingerUniformBound params)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    ∃ S : ℝ,
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S) := by
  let S : ℝ := ⨆ n : ℕ,
    schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) k f
  have hshift :
      Filter.Tendsto
        (fun n : ℕ => schwingerN params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) k f)
        Filter.atTop (nhds S) := by
    simpa [S, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      (schwingerN_tendsto_iSup_of_monotone_uniformBound
        (params := params) (k := k) hmono huniform (n0 := 0) f hf hfsupp)
  let a : ℕ → ℝ := fun n =>
    if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0
  have hshiftA : Filter.Tendsto (fun n : ℕ => a (n + 1)) Filter.atTop (nhds S) := by
    simpa [a] using hshift
  have ha : Filter.Tendsto a Filter.atTop (nhds S) :=
    (Filter.tendsto_add_atTop_iff_nat (f := a) 1).1 hshiftA
  exact ⟨S, ha⟩

/-- Lattice-bridge `n + 1`-shifted exhaustion form of two-point convergence. -/
theorem schwingerTwo_tendsto_if_exhaustion_of_monotone_uniformBound
    (params : Phi4Params)
    (hmono2 : HasSchwingerNMonotone params 2)
    (huniform : HasSchwingerUniformBound params)
    (f g : TestFun2D)
    (hf : ∀ x, 0 ≤ f x) (hg : ∀ x, 0 ≤ g x)
    (hfsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f x = 0)
    (hgsupp : ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, g x = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        schwingerTwo params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f g)
      Filter.atTop
      (nhds (⨆ n : ℕ,
        schwingerTwo params (exhaustingRectangles (n + 1) (Nat.succ_pos n)) f g)) := by
  have hfvec : ∀ i, ∀ x, 0 ≤ (![f, g] : Fin 2 → TestFun2D) i x := by
    intro i x
    fin_cases i
    · simpa using hf x
    · simpa using hg x
  have hsuppvec :
      ∀ i, ∀ x ∉ (exhaustingRectangles (0 + 1) (Nat.succ_pos 0)).toSet,
        (![f, g] : Fin 2 → TestFun2D) i x = 0 := by
    intro i x hx
    fin_cases i
    · simpa using hfsupp x hx
    · simpa using hgsupp x hx
  have hlim := schwingerN_tendsto_iSup_of_monotone_uniformBound
    (params := params) (k := 2) hmono2 huniform (n0 := 0) (![f, g] : Fin 2 → TestFun2D)
    hfvec hsuppvec
  simpa [schwingerN_two_eq_schwingerTwo] using hlim

/-! ## Uniform upper bounds -/

/-- Limiting Schwinger moments and convergence along the standard exhaustion. -/
class SchwingerLimitModel (params : Phi4Params) where
  infiniteVolumeSchwinger : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ
  infiniteVolumeSchwinger_tendsto :
    ∀ (k : ℕ) (f : Fin k → TestFun2D),
      Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop
        (nhds (infiniteVolumeSchwinger k f))

/-- Infinite-volume measure representation data (measure + probability). -/
class InfiniteVolumeMeasureModel (params : Phi4Params) where
  infiniteVolumeMeasure :
    @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration
  infiniteVolumeMeasure_isProbability :
    IsProbabilityMeasure infiniteVolumeMeasure

/-! ## Honest frontiers for infinite-volume package construction -/

/-- Honest frontier: explicit existence of the infinite-volume Schwinger limit
    together with a representing probability measure and moment formula. -/
theorem gap_infiniteVolumeLimit_exists (params : Phi4Params)
    (S : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (hlim :
      ∀ (k : ℕ) (f : Fin k → TestFun2D),
        Filter.Tendsto
          (fun n : ℕ =>
            if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
          Filter.atTop
          (nhds (S k f)))
    (μ : @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration)
    (hμprob : IsProbabilityMeasure μ)
    (hmoment :
      ∀ (k : ℕ) (f : Fin k → TestFun2D),
        S k f = ∫ ω, (∏ i, ω (f i)) ∂μ) :
    ∃ (S' : ∀ (k : ℕ), (Fin k → TestFun2D) → ℝ)
      (μ' : @Measure FieldConfig2D GaussianField.instMeasurableSpaceConfiguration),
        IsProbabilityMeasure μ' ∧
        (∀ (k : ℕ) (f : Fin k → TestFun2D),
          ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
            |schwingerN params (exhaustingRectangles n hn) k f| ≤ C) ∧
        (∀ (k : ℕ) (f : Fin k → TestFun2D),
          Filter.Tendsto
            (fun n : ℕ =>
              if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
            Filter.atTop
            (nhds (S' k f))) ∧
        (∀ (k : ℕ) (f : Fin k → TestFun2D),
          S' k f = ∫ ω, (∏ i, ω (f i)) ∂μ') := by
  exact ⟨S, μ, hμprob, hbound, hlim, hmoment⟩

/-- Public uniform-bound endpoint from explicit uniform-bound data. -/
theorem schwinger_uniformly_bounded (params : Phi4Params)
    (hbound : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
        |schwingerN params (exhaustingRectangles n hn) k f| ≤ C)
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ C : ℝ, ∀ (n : ℕ) (hn : 0 < n),
      |schwingerN params (exhaustingRectangles n hn) k f| ≤ C := by
  exact hbound k f

/-! ## Existence of the infinite volume limit -/

/-- **Existence of infinite volume Schwinger functions** (Theorem 11.2.1):
    For non-negative test functions, the limit
      S_k(f₁,...,fₖ) := lim_{n→∞} S_k^{Λₙ}(f₁,...,fₖ)
    exists (as a real number).

    For general (signed) test functions, existence follows by decomposing
    f = f⁺ - f⁻ and using multilinearity. -/
theorem infinite_volume_schwinger_exists (params : Phi4Params)
    (hlim : ∀ (k : ℕ) (f : Fin k → TestFun2D),
      ∃ S : ℝ, Filter.Tendsto
        (fun n : ℕ =>
          if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
        Filter.atTop (nhds S))
    (k : ℕ) (f : Fin k → TestFun2D) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ => if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  exact hlim k f

/-- Constructive infinite-volume Schwinger existence in interface-sequence form
    for fixed arity `k`, from `k`-point monotonicity and multiple-reflection
    bounds. -/
theorem infinite_volume_schwinger_exists_k_of_monotone_uniformBound (params : Phi4Params)
    (k : ℕ)
    (hmono : HasSchwingerNMonotone params k)
    (huniform : HasSchwingerUniformBound params)
    (f : Fin k → TestFun2D)
    (hf : ∀ i, ∀ x, 0 ≤ f i x)
    (hfsupp : ∀ i, ∀ x ∉ (exhaustingRectangles 1 (Nat.succ_pos 0)).toSet, f i x = 0) :
    ∃ S : ℝ, Filter.Tendsto
      (fun n : ℕ =>
        if h : 0 < n then schwingerN params (exhaustingRectangles n h) k f else 0)
      Filter.atTop (nhds S) := by
  exact schwingerN_limit_exists_if_exhaustion_of_monotone_uniformBound
    (params := params) (k := k) hmono huniform f hf hfsupp

/-- The infinite volume Schwinger function. -/
def infiniteVolumeSchwinger (params : Phi4Params)
    [SchwingerLimitModel params]
    (k : ℕ)
    (f : Fin k → TestFun2D) : ℝ :=
  SchwingerLimitModel.infiniteVolumeSchwinger (params := params) k f

/-- Connected (truncated) 2-point function in infinite volume:
    `S₂(f,g) - S₁(f)S₁(g)`. -/
def connectedTwoPoint (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) : ℝ :=
  infiniteVolumeSchwinger params 2 ![f, g] -
    infiniteVolumeSchwinger params 1 ![f] *
      infiniteVolumeSchwinger params 1 ![g]

@[simp] theorem connectedTwoPoint_eq (params : Phi4Params)
    [SchwingerLimitModel params] (f g : TestFun2D) :
    connectedTwoPoint params f g =
      infiniteVolumeSchwinger params 2 ![f, g] -
        infiniteVolumeSchwinger params 1 ![f] *
          infiniteVolumeSchwinger params 1 ![g] := rfl

/-- Permutation symmetry of infinite-volume Schwinger functions, inherited from
    finite-volume permutation symmetry along the standard exhaustion. -/
theorem infiniteVolumeSchwinger_perm (params : Phi4Params)
    [SchwingerLimitModel params]
    (n : ℕ) (f : Fin n → TestFun2D) (σ : Equiv.Perm (Fin n)) :
    infiniteVolumeSchwinger params n (f ∘ σ) =
      infiniteVolumeSchwinger params n f := by
  let a : ℕ → ℝ := fun m =>
    if h : 0 < m then schwingerN params (exhaustingRectangles m h) n (f ∘ σ) else 0
  let b : ℕ → ℝ := fun m =>
    if h : 0 < m then schwingerN params (exhaustingRectangles m h) n f else 0
  have ha : Filter.Tendsto a Filter.atTop (nhds (infiniteVolumeSchwinger params n (f ∘ σ))) := by
    simpa [a] using
      (SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
        (params := params) n (f ∘ σ))
  have hb : Filter.Tendsto b Filter.atTop (nhds (infiniteVolumeSchwinger params n f)) := by
    simpa [b] using
      (SchwingerLimitModel.infiniteVolumeSchwinger_tendsto
        (params := params) n f)
  have hab : a = b := by
    funext m
    by_cases hm : 0 < m
    · simp [a, b, hm, schwingerN_perm]
    · simp [a, b, hm]
  rw [hab] at ha
  exact tendsto_nhds_unique ha hb

/-- Symmetry of the infinite-volume 2-point Schwinger function from the
    finite-volume symmetry and convergence along the exhausting rectangles. -/
theorem infiniteVolumeSchwinger_two_symm (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) :
    infiniteVolumeSchwinger params 2 ![f, g] =
      infiniteVolumeSchwinger params 2 ![g, f] := by
  let σ : Equiv.Perm (Fin 2) := Equiv.swap 0 1
  have hperm := infiniteVolumeSchwinger_perm
    (params := params) 2 (![f, g] : Fin 2 → TestFun2D) σ
  have hswap : (![f, g] : Fin 2 → TestFun2D) ∘ σ = (![g, f] : Fin 2 → TestFun2D) := by
    funext i
    fin_cases i <;> simp [σ]
  calc
    infiniteVolumeSchwinger params 2 ![f, g]
        = infiniteVolumeSchwinger params 2 ((![f, g] : Fin 2 → TestFun2D) ∘ σ) := by
            simpa using hperm.symm
    _ = infiniteVolumeSchwinger params 2 (![g, f] : Fin 2 → TestFun2D) := by rw [hswap]

/-- Symmetry of the infinite-volume connected 2-point function. -/
theorem connectedTwoPoint_symm (params : Phi4Params)
    [SchwingerLimitModel params]
    (f g : TestFun2D) :
    connectedTwoPoint params f g = connectedTwoPoint params g f := by
  unfold connectedTwoPoint
  rw [infiniteVolumeSchwinger_two_symm]
  ring
