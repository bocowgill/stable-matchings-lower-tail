module

public import LennonPittel.PivotIncomparableDecorations
public import LennonPittel.PivotPairEnvelopeScale
public import LennonPittel.PivotVarianceClosure
public import LennonPittel.TwoStablePairPerSizeBounds

/-!
# From the labeled pair bounds to the two variance terms

For count-count pairs both orientations are long. For comparable residual
images, the orientation rectangle separates two short-cycle exceptions
from a harmonic tail.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage Asymptotics
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem sum_scoreTwoLongOrientations_le (hn : 0 < n) {b : ℝ} (hb : 0 < b) :
    (∑ μ : Matching n, ∑ ν : Matching n,
      (continuousScoreLaw n).real (scoreIncomparablePairEvent (ScoreTwoLongOrientations b) μ ν)) ≤
      longPairEnvelope (Real.exp 72) b n := by
  classical
  let S := (validPairSizeFinset n).filter fun s ↦
    b * Real.sqrt (n : ℝ) ≤ (s.1 : ℝ) ∧ b * Real.sqrt (n : ℝ) ≤ (s.2 : ℝ)
  have hS (s : ℕ × ℕ) (hs : s ∈ S) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  rw [scorePairMass_real_eq_sum_sizeMass (measurableSet_scoreTwoLongOrientations b) S ?_]
  · exact sum_twoStablePairSizeWeights_le hn S
      (fun s ↦ (scorePairSizeMass (ScoreTwoLongOrientations b) s).toReal)
      (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel (measurableSet_scoreTwoLongOrientations b)
        (hS s hs))
      (sum_twoStablePairSizeKernel_le_both_long hn S hS hb
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  · intro μ ν
    filter_upwards [ae_validPairSizes_of_scoreIncomparablePairEvent
      (ScoreTwoLongOrientations b) μ ν] with x hx he
    exact Finset.mem_filter.mpr ⟨mem_validPairSizeFinset.mpr (hx he), he.2.2.2⟩

theorem PivotCountParameters.integral_incomparableCountProductMass_le_envelope
    (q : PivotCountParameters) (hn : 0 < n) {κ : ℝ} (hb : 0 < q.lowerLength)
    (hκ : κ < q.lowerLength) (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ)) :
    (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) ≤
      longPairEnvelope (Real.exp 72) q.lowerLength n :=
  (q.integral_incomparableCountProducts_le_sum hn hκ hcap).trans
    (sum_scoreTwoLongOrientations_le hn hb)

/-- Sum the irregular orientation mass and the two short-cycle exceptions. -/
theorem sum_residualPairMass_le_regularOrientation {n L : ℕ} (hn : 0 < n)
    (hbudget : BackgroundCycleBudget n L) (hLt : (L : ℝ) ≤ Real.log n) (b : ℝ) (K : ℕ) :
    (∑ μ : Matching n, ∑ ν : Matching n, (continuousScoreLaw n).real
      (scoreIncomparablePairEvent (IsResidualPairGeometry b K L) μ ν)) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n)) +
          (1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n))) := by
  classical
  let R := IsResidualPairGeometry (n := n) b K L
  let w (s : ℕ × ℕ) := (scorePairSizeMass R s).toReal
  let S := validPairSizeFinset n
  let G := S.filter (RegularOrientationPair n L)
  let J := S.filter fun s ↦ ¬ RegularOrientationPair n L s
  have hR (μ ν : Matching n) : MeasurableSet {x | R x μ ν} :=
    measurableSet_isResidualPairGeometry b K L μ ν
  have hG (s : ℕ × ℕ) (hs : s ∈ G) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hJ (s : ℕ × ℕ) (hs : s ∈ J) : ValidPairSizes n s :=
    mem_validPairSizeFinset.mp (Finset.mem_filter.mp hs).1
  have hgood (s : ℕ × ℕ) (hs : s ∈ G) :
      w s ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
        (1 + Real.log n) * twoStablePairSizeKernel n s := by
    have hreg := (Finset.mem_filter.mp hs).2
    have hcut : L ≤ s.1 := hreg.1
    have hf := scorePairSizeMass_toReal_le_forced hR (hG s hs) hbudget.cutoff_two hcut
      hbudget.log_cutoff
    have hb := scorePairSizeMass_toReal_le_background_regular hn hbudget hR
      (fun _ _ _ h ↦ h.late_scores) (hG s hs) hreg
    calc
      _ ≤ (scorePairSizeMass (fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L) s).toReal +
          (scorePairSizeMass
            (fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L) s).toReal := by
        apply scorePairSizeMass_toReal_le_add
        intro μ ν
        exact Eventually.of_forall fun x hx _ ↦
          (scoreResidualPairEvent_subset_shortCycleExceptions hbudget.cutoff_two μ ν hx).imp
            (fun h ↦ ⟨hx.2.2.2, h⟩) (fun h ↦ ⟨hx.2.2.2, h⟩)
      _ ≤ _ := (add_le_add hf hb).trans_eq (by ring)
  have hreg_sum : (∑ s ∈ G, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) *
        ((1600 / Real.log (L : ℝ)) * ((n : ℝ) ^ 2 * (1 + Real.log n))) := by
    have hlog : 0 ≤ Real.log (L : ℝ) := by linarith [hbudget.log_cutoff]
    calc
      _ ≤ (Real.exp 72 * (1600 / Real.log (L : ℝ))) *
            (1 + Real.log n) * ((n : ℝ) ^ 2 * (1 + Real.log n)) :=
        sum_twoStablePairSizeWeights_le hn G w (by positivity) hgood
          (sum_twoStablePairSizeKernel_le_total hn G hG)
      _ = _ := by ring
  have ht : 1 ≤ Real.log (n : ℝ) :=
    (Nat.one_le_cast.mpr (Nat.le_trans (by decide : 1 ≤ 2) hbudget.cutoff_two)).trans hLt
  have hirreg_sum : (∑ s ∈ J, w s) ≤
      (Real.exp 72 * (1 + Real.log n)) * (2 * (n : ℝ) ^ 2 * (2 + 4 * Real.log (Real.log n))) :=
    sum_twoStablePairSizeWeights_le hn J w (Real.exp_pos 72).le
      (fun s hs ↦ scorePairSizeMass_toReal_le_kernel hR (hJ s hs))
      (sum_twoStablePairSizeKernel_le_not_regularOrientationPair ht hLt J hJ
        (fun s hs ↦ (Finset.mem_filter.mp hs).2))
  rw [scorePairMass_real_eq_sum_validPairSizeMass hR]
  change (∑ s ∈ S, w s) ≤ _
  rw [← Finset.sum_filter_add_sum_filter_not S (RegularOrientationPair n L)]
  exact (add_le_add hreg_sum hirreg_sum).trans_eq (by ring)

/-- Finite comparison with the actual centered count. -/
theorem PivotCountParameters.integral_comparableResidualMass_le_envelope
    (q : PivotCountParameters) {n : ℕ} {κ : ℝ} (hn : 0 < n)
    (hκb : κ < q.lowerLength) (hcap : (q.supportCap : ℝ) ≤ κ * Real.sqrt (n : ℝ))
    (hLK : q.shortCutoff ≤ q.supportCap)
    (hinc : (q.supportCap : ℝ) * (2048 * Real.log n / n) ≤ 1)
    (hbudget : BackgroundCycleBudget n q.shortCutoff)
    (hLt : (q.shortCutoff : ℝ) ≤ Real.log n) :
    (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
      residualPairEnvelope (Real.exp 72) n q.shortCutoff := by
  have h := q.integral_comparableResidualMass_le_geometry hn hκb hcap hLK hinc
  exact h.trans ((mul_le_mul_of_nonneg_left
    (sum_residualPairMass_le_regularOrientation hn hbudget hLt q.lowerLength q.supportCap)
    (by norm_num : (0 : ℝ) ≤ 2)).trans_eq (by unfold residualPairEnvelope; ring))

/-- Bounds for the actual pair integrals with the fixed logarithmic cycle cutoff. -/
theorem eventually_logarithmic_pivotPairIntegrals_le {b A B κ : ℝ}
    (hb : 0 < b) (hκ : 0 < κ) (hκb : κ < b) :
    ∀ᶠ n : ℕ in atTop,
      let q : PivotCountParameters := ⟨b, A, B, pivotDecorationSupportCap κ n,
        logarithmicCycleCutoff n⟩
      (∫ x, q.comparableResidualMass x ∂continuousScoreLaw n) ≤
        residualPairEnvelope (Real.exp 72) n (logarithmicCycleCutoff n) ∧
      (∫ x, q.incomparableCountProductMass x ∂continuousScoreLaw n) ≤
        longPairEnvelope (Real.exp 72) b n := by
  filter_upwards [eventually_logarithmic_cycle_budget,
    eventually_logarithmicCycleCutoff_le_supportCap hκ,
    eventually_pivotDecorationSupportCap_bounds hκ,
    eventually_residualEndpointIncrementBudget κ,
    eventually_gt_atTop (0 : ℕ)] with n hbudget hL hK hinc hn
  dsimp only
  let q : PivotCountParameters := ⟨b, A, B, pivotDecorationSupportCap κ n,
    logarithmicCycleCutoff n⟩
  exact ⟨q.integral_comparableResidualMass_le_envelope hn hκb hK.2.1 hL
      (hinc _ hK.2.1) hbudget (logarithmicCycleCutoff_cast_le n),
    q.integral_incomparableCountProductMass_le_envelope hn hb hκb hK.2.1⟩

private theorem comparableResidualMass_nonneg (q : PivotCountParameters)
    {n : ℕ} (x : ScoreProfile n) : 0 ≤ q.comparableResidualMass x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact mul_nonneg (q.count_mem_Icc i x).1 (q.localLaterResidual_mem_Icc i j x).1

private theorem incomparableCountProductMass_nonneg (q : PivotCountParameters)
    {n : ℕ} (x : ScoreProfile n) : 0 ≤ q.incomparableCountProductMass x := by
  apply Finset.sum_nonneg
  intro i _
  apply Finset.sum_nonneg
  intro j _
  exact Set.indicator_nonneg (fun y _ ↦
    mul_nonneg (q.count_mem_Icc i y).1 (q.count_mem_Icc j y).1) x

/-- Both remaining pair integrals are negligible with the same explicit cutoff. -/
theorem logarithmic_pivotPairIntegrals_isLittleO {b A B κ : ℝ}
    (hb : 0 < b) (hκ : 0 < κ) (hκb : κ < b) :
    ((fun n : ℕ ↦ ∫ x, PivotCountParameters.comparableResidualMass
        ⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ x
          ∂continuousScoreLaw n) =o[atTop]
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2)) ∧
    ((fun n : ℕ ↦ ∫ x, PivotCountParameters.incomparableCountProductMass
        ⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ x
          ∂continuousScoreLaw n) =o[atTop]
      (fun n : ℕ ↦ ((n : ℝ) * Real.log n) ^ 2)) := by
  constructor
  · apply isLittleO_iff.mpr
    intro e he
    filter_upwards [eventually_logarithmic_pivotPairIntegrals_le (A := A) (B := B) hb hκ hκb,
      eventually_residualPairEnvelope_le (Real.exp_pos 72).le he] with n hp he
    have hnonneg : 0 ≤ ∫ x, PivotCountParameters.comparableResidualMass
        ⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ x
          ∂continuousScoreLaw n := integral_nonneg fun x ↦ comparableResidualMass_nonneg
      (⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ : PivotCountParameters) x
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.log n))] using
      hp.1.trans he
  · apply isLittleO_iff.mpr
    intro e he
    filter_upwards [eventually_logarithmic_pivotPairIntegrals_le (A := A) (B := B) hb hκ hκb,
      eventually_longPairEnvelope_le (Real.exp_pos 72) hb he] with n hp he
    have hnonneg : 0 ≤ ∫ x, PivotCountParameters.incomparableCountProductMass
        ⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ x
          ∂continuousScoreLaw n := integral_nonneg fun x ↦
      incomparableCountProductMass_nonneg
      (⟨b, A, B, pivotDecorationSupportCap κ n, logarithmicCycleCutoff n⟩ : PivotCountParameters) x
    simpa only [Real.norm_eq_abs, abs_of_nonneg hnonneg,
      abs_of_nonneg (sq_nonneg ((n : ℝ) * Real.log n))] using hp.2.trans he

end LennonPittelFormalization
