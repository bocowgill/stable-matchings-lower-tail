module

public import LennonPittel.DAEndpointAsymptotics
public import LennonPittel.PivotEligibleAbundance

/-! # Eligible anchor abundance at fixed cutoffs -/

@[expose] public section

open Filter MeasureTheory Set
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- For fixed positive short cutoff, all errors in transferring band rotations
to their singleton anchors, including missing walk endpoints, tend to zero. -/
private theorem eventually_fixedAnchorFailure_le {b A η : ℝ} (hb : 0 < b) (hη : 0 ≤ η)
    (hband : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkBandEndpoints n \
        scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤ ENNReal.ofReal (η + δ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n
      (scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A)ᶜ ≤ ENNReal.ofReal (η + δ) := by
  let K (n : ℕ) := b * Real.sqrt (n : ℝ)
  have hK : ∀ᶠ n : ℕ in atTop, 81 ≤ K n :=
    ((Real.tendsto_sqrt_atTop.comp
      (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul_atTop hb).eventually_ge_atTop 81
  have hgeometry := tendsto_measure_badCoexposureScores_zero_of_mean_upper
    meanUpperConstant_nonneg eventually_expectedNumStableMatchings_le_meanUpper
  have hrare := (tendsto_measure_badScoreWalkBandEndpoints.add hgeometry).add
    tendsto_measure_badNonTinyRotation_zero
  simp only [add_zero] at hrare
  have hδε : 0 < δ / 2 := by positivity
  filter_upwards [eventually_scoreWalkAnchorAbundance_of_bandAbundance K hK, hband _ hδε,
    hrare.eventually_lt_const (ENNReal.ofReal_pos.mpr hδε)] with n hanchor hwalk hsmall
  let E := scoreWalkBandEndpoints n
  let W := scoreWalkBandAbundanceAtCutoffs n (K n) A
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (K n) A
  let G := goodCoexposureScores n
  let N := badNonTinyRotation n
  have hsub : Qᶜ ⊆ (E \ W) ∪ ((Eᶜ ∪ Gᶜ) ∪ N) := by
    intro x hx
    by_cases hE : x ∈ E
    · by_cases hW : x ∈ W
      · by_cases hG : x ∈ G
        · by_cases hN : x ∈ N
          · exact Or.inr (Or.inr hN)
          · exfalso
            apply hx
            refine hanchor hG hW fun μ hμ σ hσ hlen ↦ ?_
            simpa only [nonTinyRotationShare, neg_div] using
              exists_nonTiny_participant_of_not_mem_badNonTinyRotation hN hμ hσ hlen
        · exact Or.inr (Or.inl (Or.inr hG))
      · exact Or.inl ⟨hE, hW⟩
    · exact Or.inr (Or.inl (Or.inl hE))
  calc
    _ ≤ continuousScoreLaw n ((E \ W) ∪ ((Eᶜ ∪ Gᶜ) ∪ N)) := measure_mono hsub
    _ ≤ continuousScoreLaw n (E \ W) +
        ((continuousScoreLaw n Eᶜ + continuousScoreLaw n Gᶜ) + continuousScoreLaw n N) :=
      (measure_union_le _ _).trans (add_le_add le_rfl
        ((measure_union_le _ _).trans (add_le_add (measure_union_le _ _) le_rfl)))
    _ ≤ ENNReal.ofReal (η + δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hwalk hsmall.le
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) hδε.le]; congr 1; ring

/-- Keep the original walk failure budget at fixed cutoffs. The extra
conditions on locally eligible anchors cost only an arbitrarily small
additive error for sufficiently large markets. -/
theorem eventually_fixedEligibilityFailure_le {b A B η : ℝ}
    (hb : 0 < b) (hBm : 49 * A + 1 ≤ B) (hBi : 4 * (8 * A + 1) ≤ B) (hη : 0 ≤ η)
    (hband : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      continuousScoreLaw n (scoreWalkBandEndpoints n \
        scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤ ENNReal.ofReal (η + δ))
    (δ : ℝ) (hδ : 0 < δ) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (locallyEligiblePivotAbundance n b A B)ᶜ ≤
      ENNReal.ofReal (η + δ) := by
  have hrare := tendsto_measure_badPivotScoreGeometry_zero.add
    ((tendsto_measure_badShortStablePivotMaleMass A).add
      (tendsto_measure_badShortStablePivotForwardIncrement A))
  simp only [add_zero] at hrare
  have hδε : 0 < δ / 2 := by positivity
  filter_upwards [eventually_fixedAnchorFailure_le hb hη hband _ hδε,
    hrare.eventually_lt_const (ENNReal.ofReal_pos.mpr hδε), eventually_gt_atTop (0 : ℕ)]
    with n hanchor hsmall hn
  let Q := scoreWalkAnchorAbundanceAtCutoffs n (b * Real.sqrt n) A
  let G := goodPivotScoreGeometry n
  let M : Set (ScoreProfile n) :=
    badShortStablePivot pivotMaleSupportMass A ((49 * A + 1) / Real.sqrt (n : ℝ))
  let I : Set (ScoreProfile n) := badShortStablePivot pivotNormalizedForwardIncrement A
    ((4 * (8 * A + 1)) * Real.sqrt (n : ℝ))
  have hsub : (locallyEligiblePivotAbundance n b A B)ᶜ ≤ᵐ[continuousScoreLaw n]
      Qᶜ ∪ (Gᶜ ∪ (M ∪ I)) := by
    filter_upwards [ae_injective_rows n] with x ht hbad
    by_contra hx
    have hQ : x ∈ Q := by_contra fun h ↦ hx (Or.inl h)
    have hG : x ∈ G := by_contra fun h ↦ hx (Or.inr (Or.inl h))
    exact hbad (locallyEligiblePivotAbundance_of_good hn ht hG hQ hBm hBi
      (fun h ↦ hx (Or.inr (Or.inr (Or.inl h)))) (fun h ↦ hx (Or.inr (Or.inr (Or.inr h)))))
  calc
    _ ≤ continuousScoreLaw n (Qᶜ ∪ (Gᶜ ∪ (M ∪ I))) := measure_mono_ae hsub
    _ ≤ continuousScoreLaw n Qᶜ +
        (continuousScoreLaw n Gᶜ + (continuousScoreLaw n M + continuousScoreLaw n I)) :=
      (measure_union_le _ _).trans (add_le_add le_rfl
        ((measure_union_le _ _).trans (add_le_add le_rfl (measure_union_le _ _))))
    _ ≤ ENNReal.ofReal (η + δ / 2) + ENNReal.ofReal (δ / 2) := add_le_add hanchor hsmall.le
    _ = _ := by rw [← ENNReal.ofReal_add (by positivity) hδε.le]; congr 1; ring

end LennonPittelFormalization
