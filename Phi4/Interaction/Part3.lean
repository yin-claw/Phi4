/-
Copyright (c) 2026 Phi4 Contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Phi4.Interaction.Part2

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

/-
  NOTE:
  Thin `[InteractionUVModel params]` forwarding wrappers into
  `interactionWeightModel_nonempty_of_*` were removed to limit route bloat.
  Canonical path: construct `InteractionWeightModel` via an assumption-explicit
  theorem, then combine explicit nonempty UV+weight witnesses directly.
-/

/-- Core square-data composition: once UV data is promoted to
    `InteractionUVModel` and a constructive `InteractionWeightModel` endpoint is
    available, obtain `InteractionIntegrabilityModel` without route wrappers. -/
theorem interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hW : Nonempty (InteractionWeightModel params)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  rcases interactionUVModel_nonempty_of_sq_integrable_data
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq with ⟨huv⟩
  rcases hW with ⟨hweight⟩
  letI : InteractionUVModel params := huv
  letI : InteractionWeightModel params := hweight
  exact ⟨inferInstance⟩

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrability/measurability UV data (promoted to
       `InteractionUVModel`),
    2. explicit real-parameterized a.e. UV convergence for cutoffs, and
    3. per-volume bad-set decomposition data consisting of:
       - linear lower bounds outside bad sets,
       - geometric second-moment bounds for shifted cutoff exponentials, and
       - ENNReal geometric bad-set tails.

    This theorem wires the new Cauchy/AM-GM bad-part infrastructure into the
    production integrability path without introducing interface wrappers. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hdecomp :
      ∀ (Λ : Rectangle) (q : ℝ), 0 < q →
        ∃ a b : ℝ, 0 < a ∧
          ∃ bad : ℕ → Set FieldConfig2D,
            (∀ n : ℕ, MeasurableSet (bad n)) ∧
            (∀ n : ℕ,
              Integrable
                (fun ω : FieldConfig2D =>
                  Real.exp (-(q * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)))
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            (∀ (n : ℕ) (ω : FieldConfig2D), ω ∉ bad n →
              a * (n : ℝ) - b ≤ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω) ∧
            (∀ n : ℕ,
              MemLp
                (fun ω : FieldConfig2D =>
                  Real.exp ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω))
                2
                (freeFieldMeasure params.mass params.mass_pos)) ∧
            ∃ D2 r2 : ℝ,
              0 ≤ D2 ∧ 0 ≤ r2 ∧ r2 < 1 ∧
              (∀ n : ℕ,
                ∫ ω : FieldConfig2D,
                  (Real.exp
                    ((-q) * interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω)) ^ (2 : ℝ)
                  ∂(freeFieldMeasure params.mass params.mass_pos)
                ≤ D2 * r2 ^ n) ∧
              ∃ Cb rb : ℝ≥0∞,
                Cb ≠ ⊤ ∧ rb < 1 ∧
                (∀ n : ℕ,
                  (freeFieldMeasure params.mass params.mass_pos) (bad n) ≤ Cb * rb ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  refine interactionIntegrabilityModel_nonempty_from_sq_integrable_data_and_weight
    (params := params)
    hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
    hinteraction_meas hinteraction_sq ?_
  refine interactionWeightModel_nonempty_of_standardSeq_succ_tendsto_ae_and_geometric_exp_moment_bound
    (params := params) ?_ ?_ ?_
  · intro Λ
    have hstd :
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun n : ℕ => interactionCutoff params Λ (standardUVCutoffSeq n) ω)
            Filter.atTop
            (nhds (interaction params Λ ω)) :=
      interactionCutoff_standardSeq_tendsto_ae_of_tendsto_ae
        (params := params) (Λ := Λ) (hcutoff_ae Λ)
    filter_upwards [hstd] with ω hω
    exact hω.comp (Filter.tendsto_add_atTop_nat 1)
  · intro Λ n
    exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
      (params := params) hcutoff_meas Λ n
  intro Λ q hq
  rcases hdecomp Λ q hq with
    ⟨a, b, ha, bad, hbad_meas, hInt, hgood, hmem2, D2, r2, hD2, hr20, hr21, hMoment2,
      Cb, rb, hCb, hrb1, hbadMeasure⟩
  exact
    standardSeq_succ_geometric_exp_moment_bound_of_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params) (Λ := Λ) (q := q) (a := a) (b := b) hq ha
      bad hbad_meas hInt hgood hmem2
      D2 r2 hD2 hr20 hr21 hMoment2
      Cb rb hCb hrb1 hbadMeasure

/-- Construct `InteractionIntegrabilityModel` from:
    1. square-integrable/measurable UV data,
    2. per-volume geometric shifted-cutoff exponential moments at parameter `q`,
    3. geometric shifted-cutoff exponential moments at doubled parameter `2q`,
    4. linear thresholds `(a, b)` with effective ratio `exp(q * a) * r < 1`.

    The doubled-parameter moments are converted internally into the `MemLp`-2
    and second-moment decomposition data needed by the hard-core bad-set route. -/
theorem
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_threshold_geometric_exp_moment_and_double_exp_moment_geometric
    (params : Phi4Params)
    (hcutoff_meas :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        AEStronglyMeasurable (interactionCutoff params Λ κ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_sq :
      ∀ (Λ : Rectangle) (κ : UVCutoff),
        Integrable (fun ω => (interactionCutoff params Λ κ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
    (hcutoff_conv :
      ∀ (Λ : Rectangle),
        Filter.Tendsto
          (fun (κ : ℝ) => if h : 0 < κ then
            ∫ ω, (interactionCutoff params Λ ⟨κ, h⟩ ω - interaction params Λ ω) ^ 2
              ∂(freeFieldMeasure params.mass params.mass_pos)
            else 0)
          Filter.atTop
          (nhds 0))
    (hcutoff_ae :
      ∀ (Λ : Rectangle),
        ∀ᵐ ω ∂(freeFieldMeasure params.mass params.mass_pos),
          Filter.Tendsto
            (fun (κ : ℝ) => if h : 0 < κ then interactionCutoff params Λ ⟨κ, h⟩ ω else 0)
            Filter.atTop
            (nhds (interaction params Λ ω)))
    (hinteraction_meas :
      ∀ (Λ : Rectangle),
        AEStronglyMeasurable (interaction params Λ)
          (freeFieldMeasure params.mass params.mass_pos))
    (hinteraction_sq :
      ∀ (Λ : Rectangle),
        Integrable (fun ω => (interaction params Λ ω) ^ 2)
          (freeFieldMeasure params.mass params.mass_pos))
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
            ≤ D2 * r2 ^ n)) :
    Nonempty (InteractionIntegrabilityModel params) := by
  refine
    interactionIntegrabilityModel_nonempty_of_sq_integrable_data_and_linear_lower_bound_off_bad_sets_and_sq_exp_moment_geometric_and_bad_measure_geometric_ennreal
      (params := params)
      hcutoff_meas hcutoff_sq hcutoff_conv hcutoff_ae
      hinteraction_meas hinteraction_sq ?_
  intro Λ q hq
  rcases hcore Λ q hq with
    ⟨a, D, r, D2, r2, ha, hD, hr0, hrr1, hD2, hr20, hr21, hInt, hM, hInt2, hMoment2raw⟩
  let b : ℝ := 0
  let μ : Measure FieldConfig2D := freeFieldMeasure params.mass params.mass_pos
  let bad : ℕ → Set FieldConfig2D := fun n =>
    toMeasurable μ
      {ω : FieldConfig2D |
        interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b}
  rcases
      standardSeq_succ_sq_exp_moment_data_of_double_exponential_moment_geometric_bound
        (params := params) (Λ := Λ) (q := q)
        (hcutoff_meas := fun n => by
          exact interactionCutoff_standardSeq_succ_aestronglyMeasurable
            (params := params) hcutoff_meas Λ n)
        hInt2 D2 r2 hMoment2raw with
    ⟨hmem2, hMoment2⟩
  rcases
      shifted_cutoff_bad_event_exists_ennreal_geometric_bound_of_exponential_moment_bound_linear_threshold
        (params := params) (Λ := Λ) (q := q) (a := a) (b := b) (D := D) (r := r)
        hq hD hr0 hrr1
        (hInt := fun n => by simpa [neg_mul] using hInt n)
        (hM := fun n => by simpa [neg_mul] using hM n) with
    ⟨Cb, rb, hCb, hrb1, hbadEvent⟩
  refine
    ⟨a, b, ha, bad, ?_, hInt, ?_, hmem2, D2, r2, hD2, hr20, hr21, hMoment2, Cb, rb, hCb, hrb1, ?_⟩
  · intro n
    exact measurableSet_toMeasurable μ _
  · intro n ω hω
    have hnot :
        ¬ interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b := by
      intro hlt
      exact hω ((subset_toMeasurable μ _) hlt)
    exact not_lt.mp hnot
  · intro n
    calc
      (freeFieldMeasure params.mass params.mass_pos) (bad n)
          = (freeFieldMeasure params.mass params.mass_pos)
              {ω : FieldConfig2D |
                interactionCutoff params Λ (standardUVCutoffSeq (n + 1)) ω < a * (n : ℝ) - b} := by
              simp [bad, μ, measure_toMeasurable]
      _ ≤ Cb * rb ^ n := hbadEvent n

/-- Positivity of the partition function: Z_Λ = ∫ e^{-V_Λ} dφ_C > 0. -/
theorem partition_function_pos (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    0 < ∫ ω, Real.exp (-(interaction params Λ ω))
        ∂(freeFieldMeasure params.mass params.mass_pos) := by
  letI : IsProbabilityMeasure (freeFieldMeasure params.mass params.mass_pos) :=
    freeFieldMeasure_isProbability params.mass params.mass_pos
  have hLp : MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      (1 : ℝ≥0∞) (freeFieldMeasure params.mass params.mass_pos) :=
    InteractionWeightModel.exp_interaction_Lp
      (params := params) (Λ := Λ) (p := (1 : ℝ≥0∞)) (by norm_num)
  have hIntExp : Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
      (freeFieldMeasure params.mass params.mass_pos) :=
    (memLp_one_iff_integrable.mp hLp)
  simpa using (integral_exp_pos (μ := freeFieldMeasure params.mass params.mass_pos)
    (f := fun ω => -(interaction params Λ ω)) hIntExp)

/-- Finiteness of the partition function: Z_Λ < ∞ (i.e. the exponential is integrable). -/
theorem partition_function_integrable (params : Phi4Params)
    [InteractionWeightModel params]
    (Λ : Rectangle) :
    Integrable (fun ω => Real.exp (-(interaction params Λ ω)))
        (freeFieldMeasure params.mass params.mass_pos) := by
  have hLp : MemLp (fun ω => Real.exp (-(interaction params Λ ω)))
      (1 : ℝ≥0∞) (freeFieldMeasure params.mass params.mass_pos) :=
    InteractionWeightModel.exp_interaction_Lp
      (params := params) (Λ := Λ) (p := (1 : ℝ≥0∞)) (by norm_num)
  exact (memLp_one_iff_integrable.mp hLp)

end
