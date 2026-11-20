module

public import LennonPittel.ForwardSuccessorRowLaw
public import LennonPittel.RowCompetition
public import LennonPittel.PivotSpouseBandMask

/-!
# A deterministic lower comparison for forward successor rows

Bounding every eligible competitor by its maximal share controls competition
through the full unit interval. The deficit depends on the largest blocking
rectangle, the largest target share and the finite probability of no successor.
-/

@[expose] public section

open Filter MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

private theorem sum_embedding_le_sum {α β : Type*} [Fintype α] [Fintype β]
    (e : α ↪ β) {f : β → ℝ} (hf : ∀ i, 0 ≤ f i) :
    (∑ i, f (e i)) ≤ ∑ i, f i := by
  rw [← Finset.sum_map]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun i _ _ ↦ hf i

private theorem rowEligibilityProbability_le_scaled {x y M : ℝ}
    (hx : x ∈ Ico (0 : ℝ) 1) (hy : y ∈ Icc (0 : ℝ) 1) (hM : M < 1)
    (hxy : x * y ≤ M) :
    rowEligibilityProbability x y ≤ ((1 - x) / (1 - M)) * y := by
  unfold rowEligibilityProbability
  rw [div_mul_eq_mul_div]
  exact div_le_div_of_nonneg_left (mul_nonneg (sub_nonneg.mpr hx.2.le) hy.1)
    (sub_pos.mpr hM) (sub_le_sub_left hxy 1)

/-- A distinguished candidate competes with any subset of the reference labels.
The largest target share and the empty-row probability control its deficit. -/
theorem forwardSuccessorIntegral_ge {ι κ : Type*} [Fintype ι] [Fintype κ]
    (e : κ ↪ ι) (j : ι) {x : ℝ} {y : ι → ℝ} {M P : ℝ}
    (hx : x ∈ Ico 0 1) (hy : ∀ i, y i ∈ Icc 0 1) (hY : 0 < ∑ i, y i)
    (hM : M ∈ Ico 0 1) (hxy : ∀ i, x * y i ≤ M)
    (hP : 0 < P) (hshare : ∀ i, y i / ∑ k, y k ≤ P) :
    (1 - min 1 (M + P + Real.exp (-((1 - x) * ∑ k, y k)))) * (y j / ∑ k, y k) ≤
      rowEligibilityProbability x (y j) *
        scoreRowMass Finset.univ (fun k ↦ rowEligibilityProbability x (y (e k))) 0 1 := by
  let Y := ∑ k, y k
  let c := (1 - x) / (1 - M)
  let A := c * Y
  let b := min 1 (A * P)
  let z := Real.exp (-((1 - x) * Y))
  let a (k : κ) := rowEligibilityProbability x (y (e k))
  have hc : 0 < c := div_pos (sub_pos.mpr hx.2) (sub_pos.mpr hM.2)
  have hA : 0 < A := mul_pos hc hY
  have hb : 0 < b := lt_min zero_lt_one (mul_pos hA hP)
  have ha (k : κ) : a k ≤ c * y (e k) :=
    rowEligibilityProbability_le_scaled hx (hy _) hM.2 (hxy _)
  have hab (k : κ) : a k ∈ Icc 0 b := by
    refine ⟨rowEligibilityProbability_nonneg hx (hy _), le_min
      (rowEligibilityProbability_le_one hx (hy _)) ((ha k).trans ?_)⟩
    have h := mul_le_mul_of_nonneg_left ((div_le_iff₀ hY).mp (hshare (e k))) hc.le
    change c * y (e k) ≤ c * (P * Y) at h
    simpa only [A, mul_assoc, mul_comm P Y] using h
  have hsum : ∑ k, a k ≤ A := calc
    _ ≤ ∑ k, c * y (e k) := Finset.sum_le_sum fun k _ ↦ ha k
    _ ≤ _ := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_embedding_le_sum e fun i ↦ (hy i).1) hc.le
  have hU : (1 - x) * Y ≤ A := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    exact (le_div_iff₀ (sub_pos.mpr hM.2)).mpr
      (mul_le_of_le_one_right (sub_nonneg.mpr hx.2.le) (by linarith only [hM.1]))
  have hzero : 0 ≤ 1 - z := sub_nonneg.mpr <| Real.exp_le_one_iff.mpr
    (neg_nonpos.mpr (mul_nonneg (sub_nonneg.mpr hx.2.le) hY.le))
  have hK : (1 - z) / (A * (1 + P)) ≤ scoreRowMass Finset.univ a 0 1 := calc
    _ ≤ (1 - Real.exp (-A)) / (A + b) := by
      have hz : 1 - z ≤ 1 - Real.exp (-A) := sub_le_sub_left (Real.exp_le_exp.mpr (neg_le_neg hU)) 1
      apply div_le_div₀ (hzero.trans hz) hz (add_pos hA hb)
      linarith only [show b ≤ A * P from min_le_right _ _]
    _ ≤ _ := scoreRowMass_lower_bounded hb (min_le_left _ _) (fun k _ ↦ hab k) hA hsum
  have htarget := mul_le_mul (mul_le_rowEligibilityProbability hx (hy j)) hK
    (div_nonneg hzero (by positivity)) (rowEligibilityProbability_nonneg hx (hy j))
  change (1 - min 1 (M + P + z)) * (y j / Y) ≤ _
  refine le_trans ?_ htarget
  have heq : (1 - M) * (1 - z) / (1 + P) * (y j / Y) =
      ((1 - x) * y j) * ((1 - z) / (A * (1 + P))) := by
    dsimp only [A, c]
    field_simp [hY.ne', (sub_pos.mpr hx.2).ne', (sub_pos.mpr hM.2).ne']
  rw [← heq]
  apply mul_le_mul_of_nonneg_right _ (div_nonneg (hy j).1 hY.le)
  by_cases hd : M + P + z ≤ 1
  · rw [min_eq_right hd, le_div_iff₀ (by positivity : 0 < 1 + P)]
    have hz : 0 ≤ z := Real.exp_nonneg _
    nlinarith only [mul_nonneg hM.1 hz, mul_nonneg hP.le (add_nonneg (add_nonneg hM.1 hP.le) hz)]
  · rw [min_eq_left (le_of_not_ge hd), sub_self]
    exact div_nonneg (mul_nonneg (sub_nonneg.mpr hM.2.le) hzero) (by positivity)

/-- The target's share of the female spouse scores, indexed by her current husband. -/
noncomputable def forwardSpouseWeight {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2 / ∑ j, (diagonalPairAt d j).2

/-- A capped deficit for comparison with the independent reference rows. -/
noncomputable def forwardReferenceRowDeficit {n : ℕ} (d : DiagonalScorePairs n)
    (M P : ℝ) (i : Fin n) : ℝ :=
  min 1 (M + P + Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d)))

/-- The lower comparison holds for the actual normalized stable-row arc probability. -/
theorem normalizedStableScoreRowLaw_successor_ge_reference {n : ℕ} (d : DiagonalScorePairs n)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) {M P : ℝ}
    (hx : (diagonalPairAt d i).1 ∈ Ico 0 1) (hy : ∀ k, (diagonalPairAt d k).2 ∈ Icc 0 1)
    (hY : 0 < ∑ k, (diagonalPairAt d k).2) (hM : M ∈ Ico 0 1)
    (hxy : ∀ k, (diagonalPairAt d i).1 * (diagonalPairAt d k).2 ≤ M)
    (hP : 0 < P) (hshare : ∀ k, forwardSpouseWeight d k ≤ P) :
    ENNReal.ofReal ((1 - forwardReferenceRowDeficit d M P i) * forwardSpouseWeight d j.val) ≤
      normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j) := by
  let e : {k : {k : Fin n // i ≠ k} // k ≠ j} ↪ Fin n :=
    ⟨fun k ↦ k.val.val, fun _ _ h ↦ Subtype.ext (Subtype.ext h)⟩
  rw [normalizedStableScoreRowLaw_successor_eq d i j hx hy]
  exact ENNReal.ofReal_le_ofReal (forwardSuccessorIntegral_ge e j.val hx hy hY hM hxy hP hshare)

/-- A comparison suitable for the reference forest, with a global budget
on the deficit averaged by the target weights. -/
def HasForwardReferenceDeficit {n : ℕ} (d : DiagonalScorePairs n) (budget : ℝ) : Prop :=
  ∃ δ : Fin n → ℝ, (∀ i, δ i ∈ Icc 0 1) ∧
    (∑ i, forwardSpouseWeight d i * δ i) ≤ budget ∧
    ∀ (i : Fin n) (j : {j : Fin n // i ≠ j}),
      ENNReal.ofReal ((1 - δ i) * forwardSpouseWeight d j.val) ≤
        normalizedStableScoreRowLaw d i (scoreRowSuccessorEvent d i j)

/-- The mass defect plus the square correction in the reference forest bound. -/
theorem referenceForestError_le {ι : Type*} [Fintype ι] {p δ : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (htotal : ∑ i, p i = 1) (hδ : ∀ i, δ i ∈ Icc 0 1) :
    let u (i : ι) := (1 - δ i) * p i
    1 - (∑ i, u i) + (∑ i, u i ^ 2) ≤ (∑ i, p i * δ i) + (∑ i, p i ^ 2) := by
  dsimp only
  have hdef : 1 - (∑ i, (1 - δ i) * p i) = ∑ i, p i * δ i := by
    simp only [sub_mul, one_mul, Finset.sum_sub_distrib, htotal, sub_sub_cancel,
      mul_comm (δ _) (p _)]
  rw [hdef]
  refine add_le_add le_rfl ?_
  apply Finset.sum_le_sum
  intro i _
  apply pow_le_pow_left₀ (mul_nonneg (sub_nonneg.mpr (hδ i).2) (hp i)) _ 2
  exact mul_le_of_le_one_left (hp i) (by linarith only [(hδ i).1])

private theorem eventually_forwardReferenceScales :
    ∀ᶠ n : ℕ in atTop, 1 < n ∧
      192 * Real.log (n : ℝ) ^ 2 / n ≤ (n : ℝ) ^ (-3 / 4 : ℝ) ∧
      12 * Real.log n / n ≤ (n : ℝ) ^ (-3 / 4 : ℝ) := by
  have hcast := tendsto_natCast_atTop_atTop (R := ℝ)
  have hbound := (((isLittleO_log_rpow_rpow_atTop (s := (1 / 4 : ℝ)) 2
    (by norm_num)).const_mul_left 192).comp_tendsto hcast).eventuallyLE
  filter_upwards [eventually_gt_atTop (1 : ℕ),
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1, hbound] with n hn hlog hbound
  have hn₀ : 0 < (n : ℝ) := Nat.cast_pos.mpr (by omega)
  change |192 * Real.log (n : ℝ) ^ (2 : ℝ)| ≤ |(n : ℝ) ^ (1 / 4 : ℝ)| at hbound
  rw [Real.rpow_two, abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at hbound
  change 1 ≤ Real.log (n : ℝ) at hlog
  rw [show (-3 / 4 : ℝ) = 1 / 4 - 1 by norm_num, Real.rpow_sub_one hn₀.ne']
  exact ⟨hn, div_le_div_of_nonneg_right hbound hn₀.le,
    div_le_div_of_nonneg_right (le_trans (by nlinarith [sq_nonneg (Real.log n - 1)]) hbound) hn₀.le⟩
/-- On the regular diagonal geometry and weighted endpoint event, the true
row probabilities have deficit budget three times the endpoint cutoff. -/
theorem eventually_hasForwardReferenceDeficit :
    ∀ᶠ n : ℕ in atTop, ∀ d : DiagonalScorePairs n,
      (∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1) →
      (∀ i, (diagonalPairAt d i).2 ∈ Icc 0 1) →
      2 ≤ pivotDiagonalFemaleTotal d →
      (∀ i, forwardSpouseWeight d i ≤ 12 * Real.log n / n) →
      (∀ i, (diagonalPairAt d i).1 ≤ 8 * Real.log n / (pivotDiagonalFemaleTotal d - 1)) →
      (∑ i, forwardSpouseWeight d i *
        Real.exp (-((1 - (diagonalPairAt d i).1) * pivotDiagonalFemaleTotal d))) ≤
        (n : ℝ) ^ (-3 / 4 : ℝ) →
      HasForwardReferenceDeficit d (3 * (n : ℝ) ^ (-3 / 4 : ℝ)) := by
  filter_upwards [eventually_forwardReferenceScales] with n ⟨hn, hMbound, hPbound⟩
  intro d hx hy hY hweight hmale hend
  let Y := pivotDiagonalFemaleTotal d
  let T : ℝ := (n : ℝ) ^ (-3 / 4 : ℝ)
  let M : ℝ := 192 * Real.log (n : ℝ) ^ 2 / n
  let P : ℝ := 12 * Real.log n / n
  have hn₁ : 1 < (n : ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (n : ℝ) := by linarith only [hn₁]
  have hlog₀ := (Real.log_pos hn₁).le
  have hY' : 2 ≤ Y := hY
  have hY₀ : 0 < Y := by linarith only [hY']
  have hT : T < 1 := by
    simpa only [Real.rpow_zero] using Real.rpow_lt_rpow_of_exponent_lt hn₁
      (show (-3 / 4 : ℝ) < 0 by norm_num)
  have hM : M ∈ Ico 0 1 := ⟨by unfold M; positivity, hMbound.trans_lt hT⟩
  have hP : 0 < P := div_pos (mul_pos (by norm_num) (Real.log_pos hn₁)) hn₀
  have hweight₀ (i : Fin n) : 0 ≤ forwardSpouseWeight d i := div_nonneg (hy i).1 hY₀.le
  have hweights : ∑ i, forwardSpouseWeight d i = 1 := by
    unfold forwardSpouseWeight
    rw [← Finset.sum_div]
    change Y / Y = 1
    exact div_self hY₀.ne'
  have hyraw (j : Fin n) :
      (diagonalPairAt d j).2 = Y * forwardSpouseWeight d j := by
    unfold forwardSpouseWeight
    change (diagonalPairAt d j).2 = Y * ((diagonalPairAt d j).2 / Y)
    field_simp [hY₀.ne']
  have hprod (i j : Fin n) : (diagonalPairAt d i).1 * (diagonalPairAt d j).2 ≤ M := by
    have hrat : Y / (Y - 1) ≤ 2 :=
      (div_le_iff₀ (by linarith only [hY'])).mpr (by linarith only [hY'])
    calc
      _ ≤ (8 * Real.log n / (Y - 1)) * (diagonalPairAt d j).2 :=
        mul_le_mul_of_nonneg_right (hmale i) (hy j).1
      _ = (8 * Real.log n * (Y / (Y - 1))) * forwardSpouseWeight d j := by
        rw [hyraw]
        ring
      _ ≤ (16 * Real.log n) * forwardSpouseWeight d j := by
        apply mul_le_mul_of_nonneg_right _ (hweight₀ j)
        linarith only [mul_le_mul_of_nonneg_left hrat (by positivity : 0 ≤ 8 * Real.log (n : ℝ))]
      _ ≤ (16 * Real.log n) * (12 * Real.log n / n) :=
        mul_le_mul_of_nonneg_left (hweight j) (by positivity)
      _ = M := by unfold M; ring
  refine ⟨forwardReferenceRowDeficit d M P, fun i ↦
    ⟨le_min zero_le_one (add_nonneg (add_nonneg hM.1 hP.le) (Real.exp_nonneg _)),
      min_le_left _ _⟩, ?_, fun i j ↦
    normalizedStableScoreRowLaw_successor_ge_reference d i j (hx i) hy hY₀ hM
      (hprod i) hP hweight⟩
  calc
    _ ≤ ∑ i, forwardSpouseWeight d i *
        ((M + P) + Real.exp (-((1 - (diagonalPairAt d i).1) * Y))) :=
      Finset.sum_le_sum fun i _ ↦ mul_le_mul_of_nonneg_left (min_le_right _ _) (hweight₀ i)
    _ = (M + P) + ∑ i, forwardSpouseWeight d i *
        Real.exp (-((1 - (diagonalPairAt d i).1) * Y)) := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hweights, one_mul]
    _ ≤ 3 * T := (add_le_add (add_le_add hMbound hPbound) hend).trans_eq (by ring)

end LennonPittelFormalization
