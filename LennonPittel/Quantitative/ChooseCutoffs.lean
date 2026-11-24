module

public import LennonPittel.LennonPittelLowerTailCriterion
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Cutoff choice for the fixed-threshold lower tail -/

@[expose] public section

open Filter Real StableMarriage MeasureTheory
open scoped Topology

namespace LennonPittelFormalization

/-- The closed lower-tail probability at a fixed multiple of the classical scale. -/
noncomputable def fixedThresholdLimsup (t : ℝ) : ℝ :=
  limsup (fun n : ℕ ↦ ((uniformProfile n).toMeasure
    {p | (numStableMatchings p : ℝ) ≤ t * ((n : ℝ) * log n)}).toReal) atTop

/-- Translate the measure-valued bound furnished by the centered-moment lemma. -/
theorem fixedThresholdLimsup_le_of_measure {t η : ℝ} (hη : 0 ≤ η)
    (h : limsup (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≤ t * ((n : ℝ) * log n)}) atTop ≤ ENNReal.ofReal η) :
    fixedThresholdLimsup t ≤ η := by
  unfold fixedThresholdLimsup
  rw [ENNReal.limsup_toReal_eq (b := 1) (by simp)
    (Eventually.of_forall fun n ↦ prob_le_one (μ := (uniformProfile n).toMeasure))]
  simpa [ENNReal.toReal_ofReal hη] using ENNReal.toReal_mono ENNReal.ofReal_ne_top h

/-- Conditional last step: a two-parameter estimate on the original probability
yields the fixed-threshold rate. The constants are chosen before the threshold. -/
theorem fixedThresholdRate_of_twoCutoffs {c₀ D γ : ℝ}
    (hc : 0 < c₀) (hD : 0 < D) (hγ : 0 < γ)
    (hcut : ∀ b A : ℝ, 0 < b → b ≤ 1 → 1 ≤ A → A * b ≤ 1 / 100000 →
      fixedThresholdLimsup (c₀ * b / A) ≤ D * (b^2 + exp (-γ * A^2))) :
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      fixedThresholdLimsup t ≤ C * t^2 * log (exp 1 / t) := by
  let C := D * (2 / (γ * c₀^2) + 1)
  have hlogt : Tendsto (fun t : ℝ ↦ log t * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using tendsto_log_mul_rpow_nhdsGT_zero (r := 1) zero_lt_one
  have htend : Tendsto (fun t : ℝ ↦ t - log t * t) (𝓝[>] 0) (𝓝 0) := by
    simpa using (tendsto_id.mono_left nhdsWithin_le_nhds).sub hlogt
  suffices H : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      fixedThresholdLimsup t ≤ C * t^2 * log (exp 1 / t) by
    obtain ⟨t₀, ht₀, hI⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp H
    exact ⟨C, t₀, by dsimp [C]; positivity, ht₀, fun _ ht hlt ↦ hI ⟨ht,hlt⟩⟩
  filter_upwards [eventually_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)),
    tendsto_log_nhdsGT_zero.eventually_le_atBot (min 0 (1 - γ / 2)),
    htend.eventually_lt_const (show 0 < c₀ * γ / 200000 by positivity)]
    with t ht hl hsmall
  have ht' : 0 < t := ht
  have hl₁ : 0 ≤ -log t := neg_nonneg.mpr (hl.trans (min_le_left _ _))
  have hl₂ := hl.trans (min_le_right _ _)
  let L := 1 - log t
  let A := sqrt (2 * L / γ)
  let b := t * A / c₀
  have hL : 1 ≤ L := by dsimp [L]; linarith
  have hscale : 1 ≤ 2 * L / γ := by
    apply (le_div_iff₀ hγ).2
    dsimp [L]
    linarith
  have hA : 1 ≤ A := by
    simpa [A] using sqrt_le_sqrt hscale
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hA2 : A^2 = 2 * L / γ := sq_sqrt (zero_le_one.trans hscale)
  have hb : 0 < b := by dsimp [b]; positivity
  have hab : A * b ≤ 1 / 100000 := calc
    A * b = (2 * (t - log t * t)) / (γ * c₀) := by
      calc
        A * b = t * A^2 / c₀ := by dsimp [b]; ring
        _ = _ := by rw [hA2]; dsimp [L]; ring
    _ ≤ _ := by
      apply (div_le_iff₀ (mul_pos hγ hc)).2
      linarith only [hsmall, mul_comm c₀ γ]
  have hb₁ : b ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_right hA hb.le
    linarith
  have hthreshold : c₀ * b / A = t := by dsimp [b]; field_simp
  specialize hcut b A hb hb₁ hA hab
  rw [hthreshold] at hcut
  have hlog : log (exp 1 / t) = L := by
    simp [L, log_div (exp_pos _).ne' ht'.ne']
  have hb2 : b^2 = 2 / (γ * c₀^2) * (t^2 * L) := by
    dsimp [b]
    rw [div_pow, mul_pow, hA2]
    ring
  have hexp : exp (-γ * A^2) ≤ t^2 := calc
    _ ≤ exp (log t + log t) := by
      apply exp_le_exp.mpr
      rw [hA2]
      field_simp
      dsimp [L]
      nlinarith
    _ = _ := by rw [exp_add,exp_log ht',pow_two]
  rw [hlog]
  calc
    _ ≤ _ := hcut
    _ ≤ D * (2 / (γ * c₀^2) * (t^2 * L) + t^2 * L) := by
      rw [hb2]
      gcongr
      exact hexp.trans (le_mul_of_one_le_right (sq_nonneg t) hL)
    _ = C * t^2 * L := by dsimp [C]; ring

end LennonPittelFormalization
