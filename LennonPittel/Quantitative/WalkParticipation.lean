module

public import LennonPittel.Quantitative.Participation
public import LennonPittel.Quantitative.WalkBudgets

/-! # The walk at fixed length cutoffs -/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- Bounding each rotation by its full length gives a bounded sequence of
normalized expectations. Thus a real limsup controls all sufficiently large markets. -/
private theorem eventually_participation_le_of_limsup (g : ℕ → ℕ → ℝ)
    (hg : ∀ n k, 0 ≤ g n k ∧ g n k ≤ k)
    {q ε : ℝ} (hlim : limsup (normalizedParticipation g) atTop ≤ q) (hε : 0 < ε) :
    ∀ᶠ n in atTop, normalizedParticipation g n ≤ q + ε := by
  have hsum : ∀ᶠ n : ℕ in atTop, (∑ k ∈ Finset.Icc 2 n, g n k * singletonLengthEnvelope n k) ≤
      longGaussianMassConstant := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    refine le_trans (b := ∑ k ∈ Finset.Icc 2 n,
      longRotationLengthWeight (0 * Real.sqrt n) k * singletonLengthEnvelope n k) ?_ ?_
    · apply Finset.sum_le_sum
      intro k hk
      have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by have := (Finset.mem_Icc.mp hk).1; omega)
      simpa only [zero_mul, longRotationLengthWeight, ite_eq_left hkpos] using
        mul_le_mul_of_nonneg_right (hg n k).2 (singletonLengthEnvelope_nonneg n k)
    · simpa using (longEnvelopeSum_gaussian_le hn (ha := (le_refl (0 : ℝ))))
  have h := eventually_normalizedRotationWeight_le g (fun _ ↦ longGaussianMassConstant)
    (fun n k ↦ (hg n k).1) (fun n k hk ↦ (hg n k).2.trans (by exact_mod_cast (Finset.mem_Icc.mp hk).2)) hsum
  have hdec : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-3 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp tendsto_natCast_atTop_atTop
  have hbounded : IsBoundedUnder (· ≤ ·) atTop (normalizedParticipation g) :=
    (((tendsto_const_nhds (x := meanUpperConstant * longGaussianMassConstant)).add hdec).isBoundedUnder_le).mono_le h
  exact (eventually_lt_of_limsup_lt (hlim.trans_lt (lt_add_of_pos_right q hε)) hbounded).mono
    fun _ hlt ↦ hlt.le

/-- An absolute fixed-cutoff walk failure budget, on the endpoint event. -/
theorem fixedThreshold_walkBandFailure :
    ∃ D : ℝ, 0 < D ∧ ∀ (b A : ℝ), 0 ≤ b → 1 ≤ A → ∀ δ : ℝ, 0 < δ →
      ∀ᶠ n : ℕ in atTop, continuousScoreLaw n (scoreWalkBandEndpoints n \
        scoreWalkBandAbundanceAtCutoffs n (b * Real.sqrt n) A) ≤
          ENNReal.ofReal (δ + 50 * D * (b ^ 2 + Real.exp (-A ^ 2 / 32))) := by
  obtain ⟨D, hD, hs, hl⟩ := fixedThreshold_participation_bounds
  refine ⟨D, hD, ?_⟩
  intro b A hb hA δ hδ
  have hε : 0 < δ / 200 := by positivity
  have hshort := eventually_participation_le_of_limsup _ (fun n k ↦ by
    dsimp [shortRotationLengthWeight]
    split <;> constructor <;> first | exact le_rfl | positivity) (hs b hb) hε
  have hlong := eventually_participation_le_of_limsup _ (fun n k ↦ by
    dsimp [longRotationLengthWeight]
    split <;> constructor <;> first | exact le_rfl | positivity) (hl A (zero_le_one.trans hA)) hε
  have h := eventually_walkBandFailure_le_of_participationMeans hA (by positivity)
    (by positivity) (show 0 < δ / 2 by positivity) hshort hlong
  have hid : δ / 2 + 50 * ((D * b ^ 2 + δ / 200) +
      (D * Real.exp (-A ^ 2 / 32) + δ / 200)) =
        δ + 50 * D * (b ^ 2 + Real.exp (-A ^ 2 / 32)) := by ring
  simpa only [hid] using h

end LennonPittelFormalization
