module

public import LennonPittel.CycleQueryLaplace
public import LennonPittel.CycleLowerTail
public import LennonPittel.TwoStableBackgroundCycleTail

/-!
# Experimental background-cycle lower tails

The independent-row Laplace argument uses the same lower mean and common-row
geometry as the variance argument.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

/-- An exponential background tail under the one-sided arc comparison. -/
theorem measure_lt_commonForwardCycleCount_exp_via_laplace (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Measure.pi ν) {f | (commonForwardCycleCount C L f : ℝ) < (9 / 10 : ℝ) * Real.log L} ≤
      ENNReal.ofReal (Real.exp (-Real.log (L : ℝ) / 1600)) := by
  have h := measure_lt_background_of_cycle_laplace
    (by linarith only [hlog] : 0 < Real.log (L : ℝ))
    (integral_commonForwardCycleCount_lower_log ν C hL p hp hp₁ hδ harc harcLoss
      hlabelLoss hlog)
    (fun t ht ↦ integrable_exp_neg_mul_count (by measurability) ht)
    (fun t ht ↦ integral_exp_neg_mul_realizedForwardCycleCount_le ν
      (commonForwardCycles C (Finset.Icc 2 L)) ht)
  simpa only [commonForwardCycleCount, measureReal_def,
    ENNReal.ofReal_toReal (measure_ne_top _ _)] using
    ENNReal.ofReal_le_ofReal h

/-- The Laplace argument satisfies the original numerical background-tail interface. -/
theorem measure_lt_commonForwardCycleCount_le_via_laplace (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Measure.pi ν) {f | (commonForwardCycleCount C L f : ℝ) < (9 / 10 : ℝ) * Real.log L} ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) :=
  (measure_lt_commonForwardCycleCount_exp_via_laplace ν C hL p hp hp₁ hδ harc
    harcLoss hlabelLoss hlog).trans (ENNReal.ofReal_le_ofReal
      (exp_neg_div_1600_le_1200_div (by linarith only [hlog])))

variable {n : ℕ} {μ ν : Matching n}

/-- The actual conditional successor graph satisfies the original tail bound by Laplace. -/
theorem jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le_via_laplace
    (d : JointSpouseScores μ ν) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X : ℝ} (hX : 0 ≤ X)
    (hgeo : HasJointBackgroundGeometry d L X)
    (hmL : ∀ i, jointManSpouseScoreLeft d i ∈ Ico 0 1)
    (hmR : ∀ i, jointManSpouseScoreRight d i ∈ Ico 0 1)
    (hfL : ∀ w, jointWomanSpouseScoreLeft d w ∈ Icc 0 1)
    (hfR : ∀ w, jointWomanSpouseScoreRight d w ∈ Icc 0 1) :
    jointOffSpouseProbabilityLaw d {v |
      (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) : ℝ) <
        (9 / 10 : ℝ) * Real.log (L : ℝ)} ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  classical
  let : MeasurableSpace (Option (Fin n)) := ⊤
  let : DiscreteMeasurableSpace (Option (Fin n)) := ⟨fun _ ↦ trivial⟩
  let C := jointBackgroundLabels μ ν
  let p := jointBackgroundWeight d
  let r := jointCommonSuccessorLaw d
  have hpos := (jointOffSpouseScoreLaw_nonblocking_pos d hmL hmR).ne'
  let (i : Fin n) : IsProbabilityMeasure (r i) :=
    jointCommonSuccessorLaw_isProbabilityMeasure d hpos i
  have hp : ∀ i, 0 ≤ p i := jointBackgroundWeight_nonneg d hfR hgeo.total_pos
  let E : Set (Fin n → Option (Fin n)) := {f | (commonForwardCycleCount C L f : ℝ) <
    (9 / 10 : ℝ) * Real.log (L : ℝ)}
  change jointOffSpouseProbabilityLaw d (jointCommonSuccessors d ⁻¹' E) ≤ _
  rw [(measurePreserving_jointCommonSuccessors d hpos).measure_preimage
    (MeasurableSet.of_discrete : MeasurableSet E).nullMeasurableSet]
  exact measure_lt_commonForwardCycleCount_le_via_laplace r C hL p hp
    (sum_jointBackgroundWeight d hgeo.total_pos) (hgeo.arcError_mem hL hX) (hgeo.arcLower hmR hfL hfR)
    hgeo.arc_loss hgeo.label_loss hlog

/-- The Laplace route bounds too few actual exposed background cycles almost everywhere. -/
theorem ae_jointOffSpouseProbabilityLaw_backgroundShortCycleException_le_via_laplace
    (μ ν : Matching n) {L : ℕ} (hL : 2 ≤ L) (hlog : 100 ≤ Real.log (L : ℝ))
    {X : ℝ} (hX : 0 ≤ X) :
    ∀ᵐ d ∂jointSpouseScoreLaw μ ν, d ∈ jointMarkedNonblocking μ ν →
      HasJointBackgroundGeometry d L X →
      jointOffSpouseProbabilityLaw d ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) ≤ ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  filter_upwards [ae_jointSpouse_thresholds μ ν,
    ae_jointSpouse_ae_commonForwardCycleCount_eq μ ν L] with d hd hcount
  intro hmark hgeo
  have heq : ((fun v ↦ (splitTwoMatchingScores μ ν).symm (d, v)) ⁻¹'
        backgroundShortCycleException μ ν L) =ᵐ[jointOffSpouseProbabilityLaw d]
      {v | (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
        ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)} := by
    filter_upwards [hcount] with v hv
    apply propext
    change ((backgroundShortCycles (profileOfScores ((splitTwoMatchingScores μ ν).symm
      (d, v))) μ ν L).card : ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ) ↔
        (commonForwardCycleCount (jointBackgroundLabels μ ν) L (jointCommonSuccessors d v) :
          ℝ) < (9 / 10 : ℝ) * Real.log (L : ℝ)
    rw [hv hmark]
  rw [measure_congr heq]
  exact jointOffSpouseProbabilityLaw_fewCommonSuccessorCycles_le_via_laplace d hL hlog hX hgeo
    hd.1 hd.2.1 hd.2.2.1 hd.2.2.2

end LennonPittelFormalization
