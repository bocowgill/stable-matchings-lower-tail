module

public import LennonPittel.PivotPairEnvelopeBounds
public import LennonPittel.Quantitative.FilterParameters
public import LennonPittel.Quantitative.InclusiveTail

/-! # The lower tail from eligible anchor abundance at fixed cutoffs -/

public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal

namespace LennonPittelFormalization

/-- At fixed admissible cutoffs, the limiting lower-tail failure is at most
the failure budget for eligible pivots. The factor of two in the threshold
leaves a positive gap between the count and its conditional mean. -/
theorem limsup_uniformProfile_closedLowerTail_le_of_fixedAbundance {b A η : ℝ}
    (hb : 0 < b) (hA : 1 ≤ A) (hAb : A * b ≤ 1 / 100000) (hη : 0 ≤ η)
    (hgood : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (locallyEligiblePivotAbundance n b A (50 * A))ᶜ ≤
        ENNReal.ofReal (η + δ)) :
    limsup (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≤ (3 / 5120 * b / A) * ((n : ℝ) * Real.log n)})
        atTop ≤ ENNReal.ofReal η := by
  obtain ⟨_, hB, hκ, hκb, _, _, hlabel, hcompat⟩ :=
    fixedThreshold_pivotFilterBudgets hA hb hAb
  let K := pivotDecorationSupportCap (b / 2)
  let L := logarithmicCycleCutoff
  let q (n : ℕ) := PivotCountParameters.mk b A (50 * A) (K n) (L n)
  have hApos := zero_lt_one.trans_le hA
  have hK : ∀ᶠ n in atTop, 2 ≤ K n ∧ (K n : ℝ) ≤ (b / 2) * Real.sqrt (n : ℝ) :=
    (eventually_pivotDecorationSupportCap_bounds hκ).mono fun _ h ↦ ⟨h.1, h.2.1⟩
  obtain ⟨hR, hC⟩ := logarithmic_pivotPairIntegrals_isLittleO (A := A) (B := 50 * A) hb hκ hκb
  have hgap : 3 / 5120 * b / A < 3 * (b / 2) / (1280 * A) := by
    rw [show 3 * (b / 2) / (1280 * A) = 3 / 2560 * b / A by
      field_simp
      norm_num]
    exact (div_lt_div_iff_of_pos_right hApos).2 (by linarith)
  refine Quantitative.limsup_uniformProfile_closedLowerTail_le
    (T := fun n ↦ (q n).aggregateCount n) (M := fun n ↦ (q n).aggregateMean n)
    (fun _ ↦ measurable_totalLocalFilteredDecorationCount _ _ _ _ _)
    (fun _ ↦ measurable_totalLocalPivotConditionalMean _ _ _ _ _)
    ?_ ?_ hgap hη ?_ ?_
  · filter_upwards [hK, eventually_gt_atTop (0 : ℕ)] with n hnK hn
    exact ae_totalLocalFilteredDecorationCount_le hn hκb hnK.2
  · filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact mul_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  · intro δ hδ
    exact eventually_pivotMean_large_of_abundance L (add_nonneg hη hδ.le) hApos hB.le hκ
      tendsto_logarithmicCycleCutoff hlabel hcompat (hgood δ hδ)
  · intro e he
    exact eventually_scaledCenteredCountMoment_le_of_pair_terms b A (50 * A) (b / 2) K L
      hb hApos.le hB.le hκ.le hK tendsto_logarithmicCycleCutoff hlabel hcompat hR hC he

end LennonPittelFormalization
