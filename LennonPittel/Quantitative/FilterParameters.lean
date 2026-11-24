module

public import LennonPittel.PivotVarianceClosure

/-! # Eligibility and filter conditions at fixed cutoffs -/

@[expose] public section

namespace LennonPittelFormalization

/-- The fixed cutoffs satisfy the local eligibility bounds and the label and
compatibility budgets used by the centered-moment theorem. -/
theorem fixedThreshold_pivotFilterBudgets {A b : ℝ}
    (hA : 1 ≤ A) (hb : 0 < b) (hab : A * b ≤ 1 / 100000) :
    let B := 50 * A
    let κ := b / 2
    b ≤ 1 ∧ 0 < B ∧ 0 < κ ∧ κ < b ∧
    49 * A + 1 ≤ B ∧ 4 * (8 * A + 1) ≤ B ∧
    24 * κ ^ 2 / 2 + (B + 1) * κ ≤ 1 / 4 ∧
    Real.exp (κ * (2 * (1 + B))) * (2 * κ * (B / (1 / 128))) ≤ 3 / 32 := by
  dsimp only
  have hbSmall : b ≤ 1 / 100000 := (le_mul_of_one_le_left hb.le hA).trans hab
  have hbOne : b ≤ 1 := by linarith
  refine ⟨hbOne, by linarith, by linarith, by linarith, by linarith, by linarith, ?_, ?_⟩
  · nlinarith [mul_nonneg hb.le (sub_nonneg.mpr hbOne)]
  · have he : b / 2 * (2 * (1 + 50 * A)) ≤ 1 / 4 := by nlinarith
    have hExp : Real.exp (b / 2 * (2 * (1 + 50 * A))) ≤ 4 / 3 := calc
      _ ≤ Real.exp (1 / 4) := Real.exp_le_exp.mpr he
      _ ≤ 1 / (1 - (1 / 4 : ℝ)) :=
        Real.exp_bound_div_one_sub_of_interval (by norm_num) (by norm_num)
      _ = _ := by norm_num
    have hCoeff : 2 * (b / 2) * (50 * A / (1 / 128)) ≤ 8 / 125 := by nlinarith
    calc
      _ ≤ (4 / 3 : ℝ) * (8 / 125) :=
        mul_le_mul hExp hCoeff (by positivity) (by norm_num)
      _ ≤ _ := by norm_num

end LennonPittelFormalization
