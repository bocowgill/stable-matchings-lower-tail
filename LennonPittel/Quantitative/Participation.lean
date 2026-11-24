module

public import LennonPittel.Quantitative.ShortRate
public import LennonPittel.Quantitative.LongRate
public import LennonPittel.Quantitative.MarkedBridge

/-! # Short and long rotation participation bounds -/

@[expose] public section

open Filter Finset MeasureTheory StableMarriage
open scoped Topology

namespace LennonPittelFormalization

/-- Expected total participation with the specified length weight, divided by n log n. -/
noncomputable def normalizedParticipation (g : ℕ → ℕ → ℝ) (n : ℕ) : ℝ :=
  (∫ p, profileSingletonAnchorLengthWeight p (g n) ∂(uniformProfile n).toMeasure) /
    ((n : ℝ) * Real.log n)

/-- Both cutoff losses under the uniform preference law, with one absolute
constant. The strict length tests are the same ones used by the walk. -/
theorem fixedThreshold_participation_bounds :
    ∃ D : ℝ, 0 < D ∧
      (∀ b : ℝ, 0 ≤ b → limsup (normalizedParticipation
        (fun n ↦ shortRotationLengthWeight (b * Real.sqrt n))) atTop ≤ D * b^2) ∧
      (∀ A : ℝ, 0 ≤ A → limsup (normalizedParticipation
        (fun n ↦ longRotationLengthWeight (A * Real.sqrt n))) atTop ≤
          D * Real.exp (-A^2 / 32)) := by
  let Ds := meanUpperConstant * (Real.exp 5 * 24)
  let Dl := meanUpperConstant * longGaussianMassConstant
  let D := max 1 (max Ds Dl)
  refine ⟨D, zero_lt_one.trans_le (le_max_left ..), ?_, ?_⟩
  · intro b hb
    let g (n : ℕ) := shortRotationLengthWeight (b * Real.sqrt n)
    have hg (n k : ℕ) : 0 ≤ g n k := by dsimp [g, shortRotationLengthWeight]; split <;> positivity
    have hcap (n k : ℕ) (hk : k ∈ Icc 2 n) : g n k ≤ (n : ℝ) := by
      dsimp [g, shortRotationLengthWeight]
      split
      · exact_mod_cast (mem_Icc.mp hk).2
      · positivity
    have hsum := (eventually_gt_atTop (0 : ℕ)).mono fun n hn ↦
      Quantitative.shortEnvelopeSum_sqrt_le hn hb
    refine (limsup_normalizedRotationWeight_le g _ hg hcap hsum
      (Quantitative.tendsto_shortEnvelopeMajorant b)).trans ?_
    calc
      _ = Ds * b^2 := by dsimp [Ds]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_left Ds Dl).trans (le_max_right 1 _)) (sq_nonneg _)
  · intro A hA
    let g (n : ℕ) := longRotationLengthWeight (A * Real.sqrt n)
    have hg (n k : ℕ) : 0 ≤ g n k := by dsimp [g, longRotationLengthWeight]; split <;> positivity
    have hcap (n k : ℕ) (hk : k ∈ Icc 2 n) : g n k ≤ (n : ℝ) := by
      dsimp [g, longRotationLengthWeight]
      split
      · exact_mod_cast (mem_Icc.mp hk).2
      · positivity
    have hsum := (eventually_gt_atTop (0 : ℕ)).mono fun n hn ↦ longEnvelopeSum_gaussian_le hn hA
    refine (limsup_normalizedRotationWeight_le g _ hg hcap hsum tendsto_const_nhds).trans ?_
    calc
      _ = Dl * Real.exp (-A^2 / 32) := by dsimp [Dl]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        ((le_max_right Ds Dl).trans (le_max_right 1 _)) (Real.exp_nonneg _)

end LennonPittelFormalization
