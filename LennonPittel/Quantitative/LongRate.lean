module

public import LennonPittel.ScoreRotationLengthBudgets

/-! # Expected participation of long rotations -/

@[expose] public section

open Filter Finset MeasureTheory StableMarriage
open scoped BigOperators Classical ENNReal

namespace LennonPittelFormalization

/-- Splitting the Gaussian at twice the size leaves a cutoff factor with exponent 1/32. -/
private theorem longGaussian_split {n k : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a)
    (hk : a * Real.sqrt (n : ℝ) < (k : ℝ)) :
    singletonLengthGaussian n k ≤
      Real.exp (-a ^ 2 / 32) * singletonLengthGaussian (2 * n) k := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hs : (a * Real.sqrt (n : ℝ)) ^ 2 ≤ (k : ℝ) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg ha (Real.sqrt_nonneg _)) hk.le 2
  rw [mul_pow, Real.sq_sqrt hn'.le] at hs
  unfold singletonLengthGaussian
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  push_cast
  field_simp
  linarith only [hs]

/-- The old unconditional Gaussian moment, used at size `2*n` with the original budgets. -/
private theorem doubledGaussian_mass_le {n : ℕ} (hn : 0 < n) (K : Finset ℕ)
    (hK : K ⊆ Icc 2 n) :
    (∑ k ∈ K, (k : ℝ) * singletonLengthGaussian (2 * n) k *
        (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ))) ≤
      108 * Real.exp 4 + 288 * Real.exp 16 := by
  have hn' : 0 < (n : ℝ) := Nat.cast_pos.mpr hn
  have hn₁ : 1 ≤ (n : ℝ) := by exact_mod_cast hn
  have hτ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
  have hsqrt : Real.sqrt (↑(2 * n) : ℝ) ≤ 2 * (n : ℝ) ^ (3 / 4 : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_ofNat, Real.sqrt_mul (by norm_num : 0 ≤ (2 : ℝ))]
    apply mul_le_mul (by norm_num : Real.sqrt 2 ≤ 2) _ (Real.sqrt_nonneg _) (by norm_num)
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num)
  have hτprod : singletonLengthBudget n * Real.sqrt (↑(2 * n) : ℝ) ≤ 54 := by
    calc
      _ ≤ (27 / (n : ℝ) ^ (3 / 4 : ℝ)) * (2 * (n : ℝ) ^ (3 / 4 : ℝ)) :=
        mul_le_mul (singletonLengthBudget_le hn) hsqrt (Real.sqrt_nonneg _) (by positivity)
      _ = 54 := by field_simp; norm_num
  have hsprod : 24 / (n : ℝ) * (↑(2 * n) : ℝ) = 48 := by push_cast; field_simp; norm_num
  let J := (Icc 2 (2 * n)).filter (fun k : ℕ ↦ (0 : ℝ) * Real.sqrt (↑(2*n) : ℝ) < (k : ℝ))
  have hsub : K ⊆ J := by
    intro k hk
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp (hK hk)
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hlo, by omega⟩, by
      simpa only [zero_mul, Nat.cast_pos] using (show 0 < k by omega)⟩
  calc
    _ ≤ ∑ k ∈ J, (k : ℝ) * singletonLengthGaussian (2 * n) k *
        (singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)) :=
      sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ ↦ by unfold singletonLengthGaussian; positivity)
    _ ≤ _ := (singletonLengthGaussian_longSum_le (show 0 < 2*n by omega) 0 hτ
      (by positivity : 0 ≤ 24 / (n : ℝ))).trans (by
        rw [neg_zero, Real.exp_zero, mul_one, mul_assoc (2 * Real.exp 4), mul_assoc (6 * Real.exp 16),
          hsprod]
        nlinarith only [mul_le_mul_of_nonneg_left hτprod (Real.exp_nonneg 4)])

/-- An absolute envelope constant for the expected long-rotation participation. -/
noncomputable def longGaussianMassConstant : ℝ :=
  Real.exp 5 * (108 * Real.exp 4 + 288 * Real.exp 16)

/-- Finite Gaussian length estimate at the actual singleton budget, uniform in both cutoffs and size. -/
theorem longEnvelopeSum_gaussian_le {n : ℕ} (hn : 0 < n) {a : ℝ} (ha : 0 ≤ a) :
    (∑ k ∈ Icc 2 n, longRotationLengthWeight (a * Real.sqrt n) k * singletonLengthEnvelope n k) ≤
      longGaussianMassConstant * Real.exp (-a ^ 2 / 32) := by
  let K := (Icc 2 n).filter fun k : ℕ ↦ a * Real.sqrt n < (k : ℝ)
  let F (k : ℕ) := singletonLengthBudget n / (k : ℝ) + 24 / (n : ℝ)
  have hτ : 0 ≤ singletonLengthBudget n := by unfold singletonLengthBudget; positivity
  have hF (k : ℕ) : 0 ≤ F k := by dsimp [F]; positivity
  calc
    _ = Real.exp 5 * ∑ k ∈ K, (k : ℝ) * singletonLengthGaussian n k * F k := by
      rw [mul_sum, sum_filter]
      refine sum_congr rfl fun k _ ↦ ?_
      by_cases hk : a * Real.sqrt n < (k : ℝ)
      · simp only [longRotationLengthWeight, singletonLengthEnvelope, F, ite_eq_left hk]
        ring
      · simp [longRotationLengthWeight, hk]
    _ ≤ Real.exp 5 * (Real.exp (-a ^ 2 / 32) *
        ∑ k ∈ K, (k : ℝ) * singletonLengthGaussian (2 * n) k * F k) := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      rw [mul_sum]
      refine sum_le_sum fun k hk ↦ ?_
      calc
        _ ≤ (k : ℝ) * (Real.exp (-a ^ 2 / 32) * singletonLengthGaussian (2 * n) k) * F k :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
            (longGaussian_split hn ha (mem_filter.mp hk).2) (Nat.cast_nonneg _)) (hF k)
        _ = _ := by ring
    _ ≤ Real.exp 5 * (Real.exp (-a ^ 2 / 32) * (108 * Real.exp 4 + 288 * Real.exp 16)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (doubledGaussian_mass_le hn K (filter_subset ..)) (Real.exp_nonneg _)) (Real.exp_nonneg _)
    _ = _ := by unfold longGaussianMassConstant; ring

end LennonPittelFormalization
