module

public import LennonPittel.PivotSingletonMarkedLength

/-! # Normalized expectations of rotation length weights -/

@[expose] public section

/-! Uniform-profile participation from an absolute upper bound on the singleton length sum. -/

open Filter MeasureTheory StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

private lemma rotationWeight_nonneg {n : ℕ} (p : Profile n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) : 0 ≤ profileSingletonAnchorLengthWeight p g := by
  classical
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  exact Finset.sum_nonneg fun μ _ ↦ ite_nonneg (Finset.sum_nonneg fun σ _ ↦
    ite_nonneg (hg _) le_rfl) le_rfl

private lemma ofReal_rotationWeight {n : ℕ} (p : Profile n) (g : ℕ → ℝ)
    (hg : ∀ k, 0 ≤ g k) : ENNReal.ofReal (profileSingletonAnchorLengthWeight p g) =
      profileSingletonAnchorLengthWeight p (fun k ↦ ENNReal.ofReal (g k)) := by
  classical
  unfold profileSingletonAnchorLengthWeight singletonAnchorLengthWeight
  rw [ENNReal.ofReal_sum_of_nonneg (fun μ _ ↦ ite_nonneg (Finset.sum_nonneg fun σ _ ↦
    ite_nonneg (hg _) le_rfl) le_rfl)]
  refine Finset.sum_congr rfl fun μ _ ↦ ?_
  split_ifs
  · rw [ENNReal.ofReal_sum_of_nonneg (fun σ _ ↦ ite_nonneg (hg _) le_rfl)]
    exact Finset.sum_congr rfl fun σ _ ↦ by split_ifs <;> simp
  · simp

private lemma eventually_rotationWeight_log_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ Real.log n :=
  (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1

/-- An upper bound on the finite length sum controls normalized profile participation,
including the contribution of the exceptional scores. -/
theorem eventually_normalizedRotationWeight_le (g : ℕ → ℕ → ℝ) (F : ℕ → ℝ)
    (hg : ∀ n k, 0 ≤ g n k)
    (hcap : ∀ n k, k ∈ Finset.Icc 2 n → g n k ≤ (n : ℝ))
    (hsum : ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.Icc 2 n, g n k * singletonLengthEnvelope n k) ≤ F n) :
    ∀ᶠ n : ℕ in atTop, (∫ p, profileSingletonAnchorLengthWeight p (g n)
      ∂(uniformProfile n).toMeasure) / ((n : ℝ) * Real.log n) ≤
        meanUpperConstant * F n + (n : ℝ) ^ (-3 : ℝ) := by
  filter_upwards [eventually_lintegral_profileSingletonAnchorLengthWeight_le_gaussian,
    eventually_expectedNumStableMatchings_le_meanUpper, hsum, eventually_rotationWeight_log_ge_one,
    eventually_gt_atTop (0 : ℕ)] with n hgauss hmean hF hlogn hn
  have hn₀ : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hL : 0 < (n : ℝ) * Real.log n := mul_pos hn₀ (zero_lt_one.trans_le hlogn)
  have hF₀ := (Finset.sum_nonneg fun k (_ : k ∈ Finset.Icc 2 n) ↦
    mul_nonneg (hg n k) (singletonLengthEnvelope_nonneg n k)).trans hF
  have hEm : 0 ≤ meanUpperConstant * ((n : ℝ) * Real.log n) :=
    mul_nonneg meanUpperConstant_nonneg hL.le
  have hsmall : 0 ≤ (n : ℝ) ^ (-3 : ℝ) := Real.rpow_nonneg hn₀.le _
  have hm := (hgauss (g n) n (hg n) (hcap n)).trans (add_le_add
    (mul_le_mul' (ENNReal.ofReal_le_ofReal hmean) (ENNReal.ofReal_le_ofReal hF)) le_rfl)
  rw [← ENNReal.ofReal_mul hEm, ← ENNReal.ofReal_mul hn₀.le,
    ← ENNReal.ofReal_add (mul_nonneg hEm hF₀) (mul_nonneg hn₀.le hsmall)] at hm
  have hE : (∫ p, profileSingletonAnchorLengthWeight p (g n) ∂(uniformProfile n).toMeasure) ≤
      meanUpperConstant * ((n : ℝ) * Real.log n) * F n + n * (n : ℝ) ^ (-3 : ℝ) := by
    apply (ENNReal.ofReal_le_ofReal_iff (add_nonneg (mul_nonneg hEm hF₀)
      (mul_nonneg hn₀.le hsmall))).mp
    rw [ofReal_integral_eq_lintegral_ofReal (memLp_one_iff_integrable.mp MemLp.of_discrete)
      (Eventually.of_forall fun p ↦ rotationWeight_nonneg p _ (hg n))]
    simpa only [ofReal_rotationWeight _ _ (hg n)] using hm
  apply (div_le_iff₀ hL).mpr
  refine hE.trans ?_
  calc
    _ ≤ meanUpperConstant * ((n : ℝ) * Real.log n) * F n +
        ((n : ℝ) * Real.log n) * (n : ℝ) ^ (-3 : ℝ) :=
      add_le_add_right (mul_le_mul_of_nonneg_right
        (le_mul_of_one_le_right hn₀.le hlogn) hsmall) _
    _ = _ := by ring

/-- A convergent majorant for the weighted singleton envelope transfers to the normalized
expected participation in an independent, uniform market. The weight can depend on market size. -/
theorem limsup_normalizedRotationWeight_le (g : ℕ → ℕ → ℝ) (F : ℕ → ℝ) {f : ℝ}
    (hg : ∀ n k, 0 ≤ g n k)
    (hcap : ∀ n k, k ∈ Finset.Icc 2 n → g n k ≤ (n : ℝ))
    (hsum : ∀ᶠ n : ℕ in atTop,
      (∑ k ∈ Finset.Icc 2 n, g n k * singletonLengthEnvelope n k) ≤ F n)
    (hlim : Tendsto F atTop (𝓝 f)) :
    limsup (fun n : ℕ ↦ (∫ p, profileSingletonAnchorLengthWeight p (g n)
      ∂(uniformProfile n).toMeasure) / ((n : ℝ) * Real.log n)) atTop ≤ meanUpperConstant * f := by
  have hdec : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (-3 : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3)).comp tendsto_natCast_atTop_atTop
  have hconv : Tendsto (fun n : ℕ ↦ meanUpperConstant * F n + (n : ℝ) ^ (-3 : ℝ))
      atTop (𝓝 (meanUpperConstant * f)) := by
    simpa only [add_zero] using (tendsto_const_nhds.mul hlim).add hdec
  apply le_of_le_of_eq (limsup_le_limsup (v := fun n : ℕ ↦
    meanUpperConstant * F n + (n : ℝ) ^ (-3 : ℝ)) ?_ ?_ hconv.isBoundedUnder_le) hconv.limsup_eq
  · exact eventually_normalizedRotationWeight_le g F hg hcap hsum
  · apply isCoboundedUnder_le_of_eventually_le (x := (0 : ℝ)) _
    filter_upwards [eventually_rotationWeight_log_ge_one] with n hn
    exact div_nonneg (integral_nonneg fun p ↦ rotationWeight_nonneg p _ (hg n))
      (mul_nonneg (Nat.cast_nonneg _) (zero_le_one.trans hn))

end LennonPittelFormalization
