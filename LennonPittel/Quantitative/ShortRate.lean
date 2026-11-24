module

public import LennonPittel.ScoreRotationLengthBudgets

/-! # Expected participation of short rotations -/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators Classical ENNReal Topology

namespace LennonPittelFormalization.Quantitative

/-- Summing the marked, strict short-length envelope before discarding length information. -/
theorem shortEnvelopeSum_le {n : ℕ} (hn : 0 < n) {x : ℝ} (hx : 0 ≤ x) :
    (∑ k ∈ Finset.Icc 2 n, shortRotationLengthWeight x k * singletonLengthEnvelope n k) ≤
      Real.exp 5 * (x * (27 / (n : ℝ) ^ (3 / 4 : ℝ)) + 24 * x ^ 2 / n) := by
  let s := (Finset.Icc 2 n).filter fun k : ℕ ↦ (k : ℝ) < x
  have hs : s ⊆ Finset.Ioc 0 ⌊x⌋₊ := by
    intro k hk
    obtain ⟨hk', hkx⟩ := Finset.mem_filter.mp hk
    exact Finset.mem_Ioc.mpr ⟨by have := (Finset.mem_Icc.mp hk').1; omega, Nat.le_floor hkx.le⟩
  have hc : (s.card : ℝ) ≤ x := by
    have hnat := Finset.card_le_card hs
    simp only [Nat.card_Ioc, Nat.sub_zero] at hnat
    exact (Nat.cast_le.mpr hnat).trans (Nat.floor_le hx)
  let u := 27 / (n : ℝ) ^ (3 / 4 : ℝ) + 24 * x / n
  have hu : 0 ≤ u := by dsimp [u]; positivity
  calc
    _ = ∑ k ∈ s, (k : ℝ) * singletonLengthEnvelope n k := by
      simp only [s, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k _
      by_cases h : (k : ℝ) < x <;> simp [shortRotationLengthWeight, h]
    _ ≤ ∑ _k ∈ s, Real.exp 5 * u := by
      apply Finset.sum_le_sum
      intro k hk
      obtain ⟨hk', hkx⟩ := Finset.mem_filter.mp hk
      have hkpos : 0 < (k : ℝ) := Nat.cast_pos.mpr (by have := (Finset.mem_Icc.mp hk').1; omega)
      have hg : singletonLengthGaussian n k ≤ 1 := by
        unfold singletonLengthGaussian
        exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _))
          (by positivity))
      have hB : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
      calc
        _ = Real.exp 5 * (singletonLengthGaussian n k *
              (singletonLengthBudget n + 24 * k / n)) := by
              unfold singletonLengthEnvelope
              field_simp [hkpos.ne']
        _ ≤ Real.exp 5 * (1 * (singletonLengthBudget n + 24 * k / n)) := by gcongr
        _ ≤ _ := by
              simp only [one_mul]
              apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg 5)
              exact add_le_add (singletonLengthBudget_le hn)
                (div_le_div_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
    _ = (s.card : ℝ) * (Real.exp 5 * u) := by simp
    _ ≤ x * (Real.exp 5 * u) := mul_le_mul_of_nonneg_right hc (by positivity)
    _ = _ := by dsimp [u]; ring

/-- Finite upper envelope for short lengths under the original scale. -/
noncomputable def shortEnvelopeMajorant (b : ℝ) (n : ℕ) : ℝ :=
  Real.exp 5 * (27 * b * (n : ℝ) ^ (-(1 / 4) : ℝ) + 24 * b ^ 2)

theorem shortEnvelopeSum_sqrt_le {n : ℕ} (hn : 0 < n) {b : ℝ} (hb : 0 ≤ b) :
    (∑ k ∈ Finset.Icc 2 n,
      shortRotationLengthWeight (b * Real.sqrt n) k * singletonLengthEnvelope n k) ≤
      shortEnvelopeMajorant b n := by
  refine (shortEnvelopeSum_le hn (mul_nonneg hb (Real.sqrt_nonneg _))).trans_eq ?_
  have h : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hq : Real.sqrt (n : ℝ) / (n : ℝ) ^ (3 / 4 : ℝ) =
      (n : ℝ) ^ (-(1 / 4) : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub h]
    norm_num
  unfold shortEnvelopeMajorant
  congr 1
  calc
    _ = 27 * b * (Real.sqrt (n : ℝ) / (n : ℝ) ^ (3 / 4 : ℝ)) +
          24 * b ^ 2 * (Real.sqrt (n : ℝ)) ^ 2 / n := by ring
    _ = _ := by rw [hq, Real.sq_sqrt h.le]; field_simp

theorem tendsto_shortEnvelopeMajorant (b : ℝ) :
    Tendsto (shortEnvelopeMajorant b) atTop (𝓝 (Real.exp 5 * (24 * b ^ 2))) := by
  have h : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-(1/4) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp tendsto_natCast_atTop_atTop
  change Tendsto (fun n : ℕ ↦ Real.exp 5 * (27 * b * (n : ℝ) ^ (-(1 / 4) : ℝ) +
    24 * b ^ 2)) atTop _
  simpa only [mul_zero, zero_add] using
    (tendsto_const_nhds (x := Real.exp 5)).mul
      (((tendsto_const_nhds (x := 27 * b)).mul h).add (tendsto_const_nhds (x := 24 * b ^ 2)))

end LennonPittelFormalization.Quantitative
