module

public import LennonPittel.MarkedSpouseAngleComparison
public import LennonPittel.SmallSpouseTotalLog

/-!
# A first-moment upper bound

Split stable marks according to their female spouse-score total. The small-total
estimate bounds the part below two. The angular estimate on the whole simplex
bounds the remaining mass.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology

namespace LennonPittelFormalization

/-- Constant in the coarse first-moment bound. -/
noncomputable def meanUpperConstant : ℝ := Real.exp 2 + 1

theorem meanUpperConstant_nonneg : 0 ≤ meanUpperConstant := by
  unfold meanUpperConstant
  positivity

/-- The expected number of stable matchings is eventually at most a fixed
multiple of the market size times its logarithm. -/
theorem eventually_expectedNumStableMatchings_le_meanUpper :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤
      meanUpperConstant * ((n : ℝ) * Real.log n) := by
  filter_upwards [eventually_sum_stable_smallSpouseTotalLog_le 0,
    (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 3,
    eventually_ge_atTop (2 : ℕ)] with n hsmall hlog hn
  change 3 ≤ Real.log (n : ℝ) at hlog
  have hnR : 2 ≤ (n : ℝ) := by exact_mod_cast hn
  have hscale : 1 ≤ (n : ℝ) * Real.log n :=
    one_le_mul_of_one_le_of_one_le (by linarith) (by linarith)
  let A (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ femaleSpouseTotal x μ < (9 / 10 : ℝ) * Real.log n}
  let B (μ : Matching n) : Set (ScoreProfile n) :=
    {x | IsScoreStable x μ ∧ 2 ≤ femaleSpouseTotal x μ}
  have hcover (μ : Matching n) : {x | IsScoreStable x μ} ⊆ A μ ∪ B μ := by
    intro x hx
    rcases le_or_gt 2 (femaleSpouseTotal x μ) with h | h
    · exact Or.inr ⟨hx, h⟩
    · exact Or.inl ⟨hx, by linarith⟩
  have hbulk : (∑ μ : Matching n, continuousScoreLaw n (B μ)) ≤
      ENNReal.ofReal (Real.exp 2 * n * Real.log n) := by
    simpa [B] using sum_measure_scoreStable_and_femaleSpouseAngle_le hn
      (A := Set.univ) MeasurableSet.univ
  apply (ENNReal.ofReal_le_ofReal_iff (mul_nonneg meanUpperConstant_nonneg
    (zero_le_one.trans hscale))).mp
  rw [← sum_measure_scoreStable_eq_expected]
  calc
    _ ≤ ∑ μ : Matching n, (continuousScoreLaw n (A μ) + continuousScoreLaw n (B μ)) :=
      Finset.sum_le_sum fun μ _ ↦ (measure_mono (hcover μ)).trans (measure_union_le _ _)
    _ ≤ ENNReal.ofReal 1 + ENNReal.ofReal (Real.exp 2 * n * Real.log n) := by
      rw [Finset.sum_add_distrib]
      exact add_le_add (by simpa [A] using hsmall) hbulk
    _ ≤ _ := by
      rw [← ENNReal.ofReal_add (by norm_num) (by positivity)]
      exact ENNReal.ofReal_le_ofReal (by unfold meanUpperConstant; linarith only [hscale])

/-- The first moment is eventually bounded by the square of the market size. -/
theorem eventually_expectedNumStableMatchings_le_sizeSq :
    ∀ᶠ n : ℕ in atTop, expectedNumStableMatchings n ≤ (n : ℝ) ^ 2 := by
  have h := (((isLittleO_log_rpow_atTop (r := (1 : ℝ)) (by norm_num)).const_mul_left
    meanUpperConstant).comp_tendsto (tendsto_natCast_atTop_atTop (R := ℝ))).eventuallyLE
  filter_upwards [eventually_expectedNumStableMatchings_le_meanUpper, h] with n hmean hlog
  have hnorm : |meanUpperConstant * Real.log (n : ℝ)| ≤ |(n : ℝ) ^ (1 : ℝ)| := hlog
  rw [Real.rpow_one, abs_of_nonneg (Nat.cast_nonneg n : (0 : ℝ) ≤ n)] at hnorm
  calc
    _ ≤ meanUpperConstant * ((n : ℝ) * Real.log n) := hmean
    _ = (n : ℝ) * (meanUpperConstant * Real.log n) := by ring
    _ ≤ (n : ℝ) * n := mul_le_mul_of_nonneg_left ((le_abs_self _).trans hnorm) (Nat.cast_nonneg n)
    _ = _ := (sq _).symm

end LennonPittelFormalization
