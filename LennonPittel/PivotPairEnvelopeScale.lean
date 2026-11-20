module

public import LennonPittel.LogarithmicCutoffs

/-!
# Pair envelopes on the squared-count scale

Sizes outside the regular rectangle cost a harmonic tail. Within the rectangle,
the two short-cycle exceptions cost an inverse logarithm of the cycle cutoff.
-/

@[expose] public section

open Filter
open scoped Topology

namespace LennonPittelFormalization

/-- Sum of the irregular-size and regular short-cycle contributions. -/
noncomputable def residualPairEnvelope (C : ℝ) (n L : ℕ) : ℝ :=
  2 * (C * (1 + Real.log n)) *
    (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
      (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n)))

private theorem residualPairEnvelope_le {C : ℝ} (hC : 0 ≤ C) {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hL : 0 < Real.log (L : ℝ)) :
    residualPairEnvelope C n L ≤
      C * (16 / Real.log n + 32 * (Real.log (Real.log n) / Real.log n) +
        12800 / Real.log (L : ℝ)) * ((n : ℝ) * Real.log n) ^ 2 := by
  let t := Real.log (n : ℝ)
  let u := Real.log (L : ℝ)
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hu : 0 < u := hL
  have hlog : 0 ≤ Real.log t := Real.log_nonneg ht
  have htwo : 1 + t ≤ 2 * t := by change 1 ≤ t at ht; linarith only [ht]
  calc
    _ ≤ 2 * (C * (2 * t)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log t) +
          (1600 / u) * ((n : ℝ) ^ 2 * (2 * t))) := by
      unfold residualPairEnvelope
      change 2 * (C * (1 + t)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log t) +
        (1600 / u) * ((n : ℝ) ^ 2 * (1 + t))) ≤ _
      gcongr
    _ = _ := by
      dsimp only [t, u] at *
      field_simp
      ring

/-- Pair bound when both orientation sizes exceed a positive square-root threshold. -/
noncomputable def longPairEnvelope (C b : ℝ) (n : ℕ) : ℝ :=
  C * (1 + Real.log n) * ((n : ℝ) ^ 2 / b ^ 2)

private theorem tendsto_log_marketSize : Tendsto (fun n : ℕ ↦ Real.log (n : ℝ)) atTop atTop :=
  Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))

/-- With the logarithmic cycle cutoff the residual envelope is negligible on the squared scale. -/
theorem eventually_residualPairEnvelope_le {C e : ℝ} (hC : 0 ≤ C) (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, residualPairEnvelope C n (logarithmicCycleCutoff n) ≤
      e * ((n : ℝ) * Real.log n) ^ 2 := by
  have h1 := (tendsto_inv_atTop_zero.comp tendsto_log_marketSize).const_mul 16
  have h2 := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp
    tendsto_log_marketSize).const_mul 32
  have h3 := tendsto_inv_log_logarithmicCycleCutoff.const_mul 12800
  have hlim : Tendsto (fun n : ℕ ↦ C * (16 / Real.log n +
      32 * (Real.log (Real.log n) / Real.log n) +
      12800 / Real.log (logarithmicCycleCutoff n : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero, Function.comp_def, id_eq, div_eq_mul_inv] using
      ((h1.add h2).add h3).const_mul C
  filter_upwards [(tendsto_order.mp hlim).2 e he, tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_logarithmicCycleCutoff.eventually_gt_atTop 0] with n h ht hL
  exact (residualPairEnvelope_le hC ht hL).trans (mul_le_mul_of_nonneg_right h.le (sq_nonneg _))

/-- The two-long-orientation bound is negligible on the squared count scale. -/
theorem eventually_longPairEnvelope_le {C b e : ℝ} (hC : 0 < C) (hb : 0 < b)
    (he : 0 < e) :
    ∀ᶠ n : ℕ in atTop, longPairEnvelope C b n ≤ e * ((n : ℝ) * Real.log n) ^ 2 := by
  filter_upwards [tendsto_log_marketSize.eventually_ge_atTop 1,
    tendsto_log_marketSize.eventually_ge_atTop (2 * C / b ^ 2 / e)] with n ht hscale
  let t := Real.log (n : ℝ)
  have htn : 0 ≤ t := zero_le_one.trans ht
  have htwo : 1 + t ≤ 2 * t := by change 1 ≤ t at ht; linarith only [ht]
  have hmul : 2 * C / b ^ 2 ≤ e * t := by
    simpa only [mul_comm e] using (div_le_iff₀ he).1 hscale
  calc
    longPairEnvelope C b n ≤ C * (2 * t) * ((n : ℝ) ^ 2 / b ^ 2) := by
      unfold longPairEnvelope
      gcongr
    _ = ((n : ℝ) ^ 2 * t) * (2 * C / b ^ 2) := by ring
    _ ≤ ((n : ℝ) ^ 2 * t) * (e * t) := mul_le_mul_of_nonneg_left hmul (by positivity)
    _ = _ := by ring

end LennonPittelFormalization
