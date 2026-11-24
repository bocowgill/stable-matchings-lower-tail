module

public import LennonPittel.Quantitative.ChooseCutoffs
public import LennonPittel.Quantitative.FixedEligibility
public import LennonPittel.Quantitative.FixedPivotTail
public import LennonPittel.Quantitative.WalkParticipation

/-! # A fixed-threshold lower-tail bound for the number of stable matchings -/

public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- For each sufficiently small fixed threshold, the lower-tail probability
has limiting upper bound of order `t^2 * log (exp 1 / t)`. -/
theorem fixedThreshold_lowerTail :
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      fixedThresholdLimsup t ≤ C * t^2 * Real.log (Real.exp 1 / t) := by
  obtain ⟨D, hD, hwalk⟩ := fixedThreshold_walkBandFailure
  refine fixedThresholdRate_of_twoCutoffs (c₀ := 3 / 5120) (D := 50 * D) (γ := 1 / 32)
    (by norm_num) (by positivity) (by norm_num) ?_
  intro b A hb _ hA hAb
  let η := 50 * D * (b^2 + Real.exp (-A^2 / 32))
  have hη : 0 ≤ η := by dsimp [η]; positivity
  obtain ⟨_, _, _, _, hBm, hBi, _, _⟩ := fixedThreshold_pivotFilterBudgets hA hb hAb
  have hband (δ : ℝ) (hδ : 0 < δ) :
      ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (scoreWalkBandEndpoints n \
        scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤ ENNReal.ofReal (η + δ) := by
    simpa only [η, add_comm δ] using hwalk b A hb.le hA δ hδ
  have helig := eventually_fixedEligibilityFailure_le hb hBm hBi hη hband
  have hcount := fixedThresholdLimsup_le_of_measure hη
    (limsup_uniformProfile_closedLowerTail_le_of_fixedAbundance hb hA hAb hη helig)
  simpa only [η, neg_div, neg_mul, div_mul_eq_mul_div, one_mul] using hcount

end LennonPittelFormalization
