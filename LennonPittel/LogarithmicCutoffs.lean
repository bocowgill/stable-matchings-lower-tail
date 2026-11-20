module

public import LennonPittel.PivotBackgroundGeometry
public import LennonPittel.PivotAggregateMean

/-!
# The logarithmic cycle cutoff

The cutoff is the integer part of the logarithm of the market size.
The rectangular orientation range bounds the omitted-label loss uniformly.
-/

@[expose] public section

open Filter
open scoped Topology BigOperators

namespace LennonPittelFormalization

/-- Maximum length of a short cycle. -/
noncomputable def logarithmicCycleCutoff (n : ℕ) : ℕ := ⌊Real.log (n : ℝ)⌋₊

theorem logarithmicCycleCutoff_cast_le (n : ℕ) :
    (logarithmicCycleCutoff n : ℝ) ≤ Real.log (n : ℝ) :=
  Nat.floor_le (Real.log_natCast_nonneg n)

theorem tendsto_logarithmicCycleCutoff : Tendsto logarithmicCycleCutoff atTop atTop :=
  tendsto_nat_floor_atTop.comp
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ)))

theorem tendsto_log_logarithmicCycleCutoff :
    Tendsto (fun n : ℕ ↦ Real.log (logarithmicCycleCutoff n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_logarithmicCycleCutoff)

theorem tendsto_inv_log_logarithmicCycleCutoff :
    Tendsto (fun n : ℕ ↦ (Real.log (logarithmicCycleCutoff n : ℝ))⁻¹) atTop (𝓝 0) :=
  tendsto_inv_atTop_zero.comp tendsto_log_logarithmicCycleCutoff

private theorem tendsto_log_natCast :
    Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- Every fixed logarithmic power is negligible against every positive power of n. -/
theorem tendsto_log_pow_div_nat_rpow (k : ℕ) {s : ℝ} (hs : 0 < s) :
    Tendsto (fun n : ℕ ↦ (Real.log (n : ℝ)) ^ k / (n : ℝ) ^ s) atTop (𝓝 0) := by
  have h := ((isLittleO_log_rpow_rpow_atTop (k : ℝ) hs).tendsto_div_nhds_zero).comp
    (tendsto_natCast_atTop_atTop (R := ℝ))
  simpa only [Function.comp_def, Real.rpow_natCast] using h

/-- Finite control of the repeated-label contribution. -/
theorem logarithmic_collision_label_bound {n : ℕ} (hn : 0 < n) :
    ((logarithmicCycleCutoff n).choose 2 : ℝ) * (2060 * Real.log (n : ℝ) / n) ≤
      2060 * (Real.log (n : ℝ)) ^ 3 / n := by
  have hL := logarithmicCycleCutoff_cast_le n
  have ht := Real.log_natCast_nonneg n
  have hc : ((logarithmicCycleCutoff n).choose 2 : ℝ) ≤ (Real.log (n : ℝ)) ^ 2 := by
    rw [Nat.cast_choose_two]
    have hsq := pow_le_pow_left₀ (Nat.cast_nonneg (logarithmicCycleCutoff n)) hL 2
    nlinarith only [hsq, Nat.cast_nonneg (α := ℝ) (logarithmicCycleCutoff n),
      sq_nonneg (logarithmicCycleCutoff n : ℝ)]
  calc
    _ ≤ (Real.log (n : ℝ)) ^ 2 * (2060 * Real.log (n : ℝ) / n) :=
      mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by ring

/-- A simple upper envelope for both label losses tends to zero. -/
theorem tendsto_logarithmic_label_envelope :
    Tendsto (fun n : ℕ ↦ 2060 * (Real.log (n : ℝ)) ^ 3 / n +
      4120 / Real.log (n : ℝ)) atTop (𝓝 0) := by
  have h1 := (tendsto_log_pow_div_nat_rpow 3 (by norm_num : (0 : ℝ) < 1)).const_mul 2060
  have h2 := (tendsto_inv_atTop_zero.comp tendsto_log_natCast).const_mul 4120
  simpa only [Real.rpow_one, mul_zero, add_zero, Function.comp_def,
    ← div_eq_mul_inv, mul_div_assoc] using h1.add h2

/-- The logarithmic short-cycle cutoff fits every positive square-root support budget. -/
theorem eventually_logarithmicCycleCutoff_le_supportCap {κ : ℝ} (hκ : 0 < κ) :
    ∀ᶠ n : ℕ in atTop, logarithmicCycleCutoff n ≤ pivotDecorationSupportCap κ n := by
  have h := tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [(tendsto_order.mp h).2 (κ / 2) (by positivity),
    eventually_pivotDecorationSupportCap_bounds hκ, eventually_gt_atTop (0 : ℕ)]
    with n hn hK hn0
  have hs : 0 < (n : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn0) _
  have hbound : Real.log (n : ℝ) ≤ κ * Real.sqrt (n : ℝ) / 2 := by
    rw [pow_one] at hn
    have hh := (div_le_iff₀ hs).1 hn.le
    rw [Real.sqrt_eq_rpow]
    linarith only [hh]
  have hKm : ((pivotDecorationSupportCap κ n - 1 : ℕ) : ℝ) ≤
      pivotDecorationSupportCap κ n := Nat.cast_le.mpr (Nat.sub_le _ _)
  exact_mod_cast (logarithmicCycleCutoff_cast_le n).trans (hbound.trans (hK.2.2.trans hKm))

/-- Label collisions and labels outside the common set have negligible total weight. -/
theorem eventually_logarithmic_label_budget :
    ∀ᶠ n : ℕ in atTop, backgroundLabelBudget n (logarithmicCycleCutoff n) ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp tendsto_logarithmic_label_envelope).2
    (1 / 100) (by norm_num), tendsto_log_natCast.eventually_gt_atTop 0,
    eventually_gt_atTop (0 : ℕ)] with n he ht hn
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hmissing :
      (logarithmicCycleCutoff n : ℝ) * (2 * n / (Real.log n) ^ 3) * backgroundWeightCeiling n ≤
        4120 / Real.log n := by
    unfold backgroundWeightCeiling
    calc
      _ ≤ Real.log n * (2 * n / (Real.log n) ^ 3) * (2060 * Real.log n / n) := by
        gcongr
        exact logarithmicCycleCutoff_cast_le n
      _ = _ := by field_simp; ring
  unfold backgroundLabelBudget
  rw [add_mul]
  exact (add_le_add (logarithmic_collision_label_bound hn) hmissing).trans he.le

/-- The relative arc-error envelope is negligible for logarithmic lengths. -/
theorem tendsto_logarithmic_arc_envelope :
    Tendsto (fun n : ℕ ↦ 16 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 10 : ℝ) +
      Real.log (n : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ)) atTop (𝓝 0) := by
  have h := (tendsto_log_pow_div_nat_rpow 2 (by norm_num : (0 : ℝ) < 1 / 10)).const_mul 16
  simpa only [mul_zero, add_zero, pow_one, mul_div_assoc] using
    h.add (tendsto_log_pow_div_nat_rpow 1 (by norm_num : (0 : ℝ) < 1 / 10))

/-- Direct finite arc hypotheses hold eventually, uniformly in the female total. -/
theorem eventually_logarithmic_arc_budget :
    ∀ᶠ n : ℕ in atTop, ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
      (logarithmicCycleCutoff n : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100 := by
  filter_upwards [(tendsto_order.mp tendsto_logarithmic_arc_envelope).2
    (1 / 100) (by norm_num), eventually_gt_atTop (0 : ℕ)] with n he hn Y hY
  have hU : 0 < (n : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hn) _
  calc
    _ ≤ Real.log (n : ℝ) * (backgroundMaleCeiling n + 1 / (n : ℝ) ^ (1 / 10 : ℝ)) :=
      mul_le_mul (logarithmicCycleCutoff_cast_le n)
        (add_le_add_right (one_div_le_one_div_of_le hU hY) _)
        (add_nonneg (by unfold backgroundMaleCeiling; positivity)
          (one_div_nonneg.mpr (hU.trans_le hY).le)) (Real.log_natCast_nonneg n)
    _ = 16 * (Real.log (n : ℝ)) ^ 2 / (n : ℝ) ^ (1 / 10 : ℝ) +
        Real.log (n : ℝ) / (n : ℝ) ^ (1 / 10 : ℝ) := by unfold backgroundMaleCeiling; ring
    _ ≤ _ := he.le

/-- The logarithmic cutoff satisfies every finite background hypothesis. -/
theorem eventually_logarithmic_cycle_budget :
    ∀ᶠ n : ℕ in atTop, BackgroundCycleBudget n (logarithmicCycleCutoff n) := by
  filter_upwards [tendsto_logarithmicCycleCutoff.eventually_ge_atTop 2,
    tendsto_log_logarithmicCycleCutoff.eventually_ge_atTop 100,
    eventually_logarithmic_arc_budget, eventually_logarithmic_label_budget] with n hL hlog ha hl
  exact ⟨hL, hlog, ha, hl⟩

end LennonPittelFormalization
