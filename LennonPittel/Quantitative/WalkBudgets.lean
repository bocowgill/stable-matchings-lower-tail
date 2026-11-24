module

public import LennonPittel.ScoreRotationBandAbundance

/-! # From expected participation to walk failure -/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- Markov's inequality for participation, pulled back along the uniform profile map. -/
private theorem participationTail_le {n : ℕ} (g : ℕ → ℝ) (hg : ∀ k, 0 ≤ g k)
    {a q : ℝ} (ha : 0 < a)
    (hm : (∫ p, profileSingletonAnchorLengthWeight p g ∂(uniformProfile n).toMeasure) / a ≤ q) :
    continuousScoreLaw n {x | (1 / 50 : ℝ) * a <
      profileSingletonAnchorLengthWeight (profileOfScores x) g} ≤ ENNReal.ofReal (50 * q) := by
  classical
  let f (p : Profile n) := profileSingletonAnchorLengthWeight p g
  let μ := (uniformProfile n).toMeasure
  have hf (p : Profile n) : 0 ≤ f p := by
    unfold f profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
    exact Finset.sum_nonneg fun μ _ ↦ ite_nonneg (Finset.sum_nonneg fun σ _ ↦
      ite_nonneg (hg _) le_rfl) le_rfl
  let c := (1 / 50 : ℝ) * a
  have hc : 0 < c := by dsimp [c]; positivity
  let E := {p : Profile n | c < f p}
  change continuousScoreLaw n (profileOfScores ⁻¹' E) ≤ _
  rw [← Measure.map_apply (measurePreserving_profileOfScores n).measurable
    (show MeasurableSet E from MeasurableSet.of_discrete), (measurePreserving_profileOfScores n).map_eq]
  change μ E ≤ _
  rw [← ofReal_measureReal (μ := μ) (s := E)]
  apply ENNReal.ofReal_le_ofReal
  have hmark := mul_meas_ge_le_integral_of_nonneg (μ := μ) (f := f)
    (Eventually.of_forall hf) (memLp_one_iff_integrable.mp MemLp.of_discrete) c
  have hsub : E ⊆ {p | c ≤ f p} := by
    intro p hp
    exact (show c < f p from hp).le
  have hE : c * μ.real E ≤ q * a :=
    ((mul_le_mul_of_nonneg_left (measureReal_mono hsub) hc.le).trans hmark).trans
      ((div_le_iff₀ ha).mp hm)
  calc
    μ.real E ≤ q * a / c := (le_div_iff₀ hc).mpr (by linarith only [hE])
    _ = 50 * q := (div_eq_iff hc.ne').mpr (by dsimp [c]; ring)

/-- At fixed cutoffs, expected short and long participation budgets control
loss of in-band walk abundance with a factor of 50 and arbitrary additive slack. -/
theorem eventually_walkBandFailure_le_of_participationMeans {b A s l δ : ℝ}
    (hA : 1 ≤ A) (hs : 0 ≤ s) (hl : 0 ≤ l) (hδ : 0 < δ)
    (hshort : ∀ᶠ n : ℕ in atTop, (∫ p, profileSingletonAnchorLengthWeight p
      (shortRotationLengthWeight (b * Real.sqrt n)) ∂(uniformProfile n).toMeasure) /
      ((n : ℝ) * Real.log n) ≤ s)
    (hlong : ∀ᶠ n : ℕ in atTop, (∫ p, profileSingletonAnchorLengthWeight p
      (longRotationLengthWeight (A * Real.sqrt n)) ∂(uniformProfile n).toMeasure) /
      ((n : ℝ) * Real.log n) ≤ l) :
    ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (scoreWalkBandEndpoints n \
      scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤ ENNReal.ofReal (δ + 50 * (s + l)) := by
  have ha : ∀ᶠ n : ℕ in atTop, 0 < (n : ℝ) * Real.log n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ)] with n hn
    exact mul_pos (by positivity) (Real.log_pos (by exact_mod_cast hn))
  rw [mul_add, ← add_assoc]
  apply eventually_measure_scoreWalkBandEndpoints_diff_abundanceAtCutoffs_le
    (fun n ↦ b * Real.sqrt n) hA hδ (by positivity) (by positivity)
  · filter_upwards [ha, hshort] with n hpos hm
    exact participationTail_le _ (fun k ↦ by unfold shortRotationLengthWeight; split <;> positivity)
      hpos hm
  · filter_upwards [ha, hlong] with n hpos hm
    exact participationTail_le _ (fun k ↦ by unfold longRotationLengthWeight; split <;> positivity)
      hpos hm

end LennonPittelFormalization
