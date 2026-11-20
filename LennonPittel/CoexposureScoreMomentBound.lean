module

public import LennonPittel.CoexposureGoodScores
public import LennonPittel.CoexposureScoreProduct
public import LennonPittel.CoexposureScoreRow
public import LennonPittel.CoexposureGaussianSum
public import LennonPittel.CoexposureScoreEstimates

/-!
# Successor bounds for good stable score profiles

The stable cells of a fixed matching form independent unnormalized rows.
The diagonal cutoffs bound the successor marginals in these rows.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped BigOperators ENNReal Topology

namespace LennonPittelFormalization

/-- The male spouse score at a diagonal entry. -/
def diagonalMale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).1

/-- The female spouse score at a diagonal entry. -/
def diagonalFemale {n : ℕ} (d : DiagonalScorePairs n) (i : Fin n) : ℝ :=
  (diagonalPairAt d i).2

/-- The sum of the female spouse scores. -/
def diagonalFemaleTotal {n : ℕ} (d : DiagonalScorePairs n) : ℝ :=
  ∑ j, diagonalFemale d j

/-- The spouse-score cutoffs expressed on diagonal data indexed by husbands. -/
def goodDiagonalScores (n : ℕ) : Set (DiagonalScorePairs n) :=
  {d | 2 ≤ diagonalFemaleTotal d ∧
    (∀ j, diagonalFemale d j / diagonalFemaleTotal d ≤ 12 * Real.log n / n) ∧
    (∀ i, diagonalMale d i ≤ 8 * Real.log n / (diagonalFemaleTotal d - 1))}

/-- Reindexing by husbands preserves each of the three spouse cutoffs. -/
theorem mem_goodDiagonalScores_iff {n : ℕ} (x : ScoreProfile n) (μ : Matching n) :
    (splitScorePairs μ x).1 ∈ goodDiagonalScores n ↔ GoodSpouseScores x μ := by
  have hy (j : Fin n) : diagonalFemale (splitScorePairs μ x).1 j =
      femaleSpouseScore x μ (μ j) := by
    simp [diagonalFemale, diagonalPairAt_splitScorePairs, femaleSpouseScore]
  have hs : diagonalFemaleTotal (splitScorePairs μ x).1 = femaleSpouseTotal x μ := by
    simp only [diagonalFemaleTotal, hy, femaleSpouseTotal]
    exact Equiv.sum_comp μ (fun j ↦ x (.inr j) (μ.symm j))
  have hall : (∀ j, femaleSpouseScore x μ (μ j) / femaleSpouseTotal x μ ≤
      12 * Real.log n / n) ↔
      ∀ j, femaleSpouseScore x μ j / femaleSpouseTotal x μ ≤ 12 * Real.log n / n :=
    ⟨fun h j ↦ by simpa only [Equiv.apply_symm_apply] using h (μ.symm j),
      fun h j ↦ h (μ j)⟩
  simp only [goodDiagonalScores, mem_ofPred_eq, GoodSpouseScores, hs, hy, diagonalMale,
    diagonalPairAt_splitScorePairs, maleSpouseScore, hall]

/-- The diagonal score cutoffs are measurable. -/
theorem measurableSet_goodDiagonalScores (n : ℕ) : MeasurableSet (goodDiagonalScores n) := by
  have hm (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalMale d i) :=
    measurable_fst.comp (measurable_pi_apply _)
  have hf (i : Fin n) : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemale d i) :=
    measurable_snd.comp (measurable_pi_apply _)
  have hs : Measurable (fun d : DiagonalScorePairs n ↦ diagonalFemaleTotal d) :=
    Finset.measurable_sum _ fun i _ ↦ hf i
  unfold goodDiagonalScores
  simp only [ofPred_and, ofPred_forall]
  exact (measurableSet_le measurable_const hs).inter
    ((MeasurableSet.iInter fun j ↦ measurableSet_le ((hf j).div hs) measurable_const).inter
      (MeasurableSet.iInter fun i ↦ measurableSet_le (hm i)
        (measurable_const.div (hs.sub measurable_const))))

private theorem diagonal_good_product_le {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j) (i j : Fin n) :
    diagonalMale d i * diagonalFemale d j ≤ 192 * (Real.log n) ^ 2 / n := by
  let s := diagonalFemaleTotal d
  have hs : 2 ≤ s := hg.1
  have hspos : 0 < s := by linarith
  have hsone : 0 < s - 1 := by linarith
  have hscale : s / (s - 1) ≤ 2 := (div_le_iff₀ hsone).2 (by linarith)
  calc
    diagonalMale d i * diagonalFemale d j =
        (diagonalMale d i * (diagonalFemale d j / s)) * s := by
          rw [mul_assoc, div_mul_cancel₀ _ hspos.ne']
    _ ≤ (8 * Real.log n / (s - 1) * (12 * Real.log n / n)) * s :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (hg.2.2 i) (hg.2.1 j) (div_nonneg (hy j) hspos.le)
          ((hx i).trans (hg.2.2 i))) hspos.le
    _ = (96 * (Real.log n) ^ 2 / n) * (s / (s - 1)) := by ring
    _ ≤ (96 * (Real.log n) ^ 2 / n) * 2 := mul_le_mul_of_nonneg_left hscale (by positivity)
    _ = _ := by ring

private theorem diagonal_competitor_sum {n : ℕ} (y : Fin n → ℝ)
    (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, y k.val.val) =
      (∑ k, y k) - y i - y j.val := by
  classical
  have houter : (∑ k : {k : Fin n // i ≠ k}, y k.val) = (∑ k, y k) - y i := by
    rw [← Finset.sum_subtype (Finset.univ.erase i) (by simp [ne_comm]) y]
    linarith [Finset.sum_erase_add Finset.univ y (Finset.mem_univ i)]
  let f := fun k : {k : Fin n // i ≠ k} ↦ y k.val
  change (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, f k.val) =
    (∑ k, y k) - y i - f j
  rw [← Finset.sum_subtype (Finset.univ.erase j) (by simp) f]
  linarith [Finset.sum_erase_add Finset.univ f (Finset.mem_univ j)]

private theorem diagonal_arc_bound {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n) (hx : ∀ i, 0 ≤ diagonalMale d i)
    (hy : ∀ j, 0 ≤ diagonalFemale d j)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i j : Fin n) :
    0 < diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j ∧
      diagonalFemale d j / ((1 - diagonalMale d i * diagonalFemale d j) *
        (diagonalFemaleTotal d - diagonalFemale d i - diagonalFemale d j)) ≤
      (1 + coexposureSuccessorPerturbation n) * (diagonalFemale d j / diagonalFemaleTotal d) := by
  let s := diagonalFemaleTotal d
  let v := diagonalFemale d j
  let a := 1 - diagonalMale d i * v
  let b := s - diagonalFemale d i - v
  have hs : 0 < s := by linarith [show 2 ≤ s from hg.1]
  have ha : 1 - 192 * (Real.log n) ^ 2 / n ≤ a := by
    linarith only [diagonal_good_product_le hg hx hy i j]
  have hapos := hA.trans_le ha
  have hb : 1 - 24 * Real.log n / n ≤ b / s := by
    dsimp only [b, v]
    rw [sub_div, sub_div, div_self hs.ne']
    have hi := hg.2.1 i
    have hj := hg.2.1 j
    change diagonalFemale d i / s ≤ 12 * Real.log n / n at hi
    change diagonalFemale d j / s ≤ 12 * Real.log n / n at hj
    linarith only [hi, hj, show (24 : ℝ) * Real.log n / n =
      12 * Real.log n / n + 12 * Real.log n / n by ring]
  have hbpos : 0 < b := (div_pos_iff_of_pos_right hs).mp (hB.trans_le hb)
  refine ⟨hbpos, ?_⟩
  change v / (a * b) ≤ (1 + coexposureSuccessorPerturbation n) * (v / s)
  calc
    _ = (a⁻¹ * (b / s)⁻¹) * (v / s) := by
      field_simp [hapos.ne', hbpos.ne', hs.ne']
    _ ≤ ((1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹) * (v / s) :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul (inv_anti₀ hA ha) (inv_anti₀ hB hb)
          (inv_nonneg.mpr (div_nonneg hbpos.le hs.le)) (inv_nonneg.mpr hA.le))
        (div_nonneg (hy j) hs.le)
    _ ≤ _ := mul_le_mul_of_nonneg_right hδ (div_nonneg (hy j) hs.le)

/-- The good diagonal bounds each arc by its female share times the
forward perturbation, with the unnormalized row mass kept explicit. -/
theorem stableScoreRowLaw_successor_le_of_goodDiagonalScores {n : ℕ} {d : DiagonalScorePairs n}
    (hg : d ∈ goodDiagonalScores n)
    (hx : ∀ i, (diagonalPairAt d i).1 ∈ Ico 0 1)
    (hy : ∀ j, (diagonalPairAt d j).2 ∈ Icc 0 1)
    (hA : 0 < 1 - 192 * (Real.log n) ^ 2 / n)
    (hB : 0 < 1 - 24 * Real.log n / n)
    (hδ : (1 - 192 * (Real.log n) ^ 2 / n)⁻¹ * (1 - 24 * Real.log n / n)⁻¹ ≤
      1 + coexposureSuccessorPerturbation n) (i : Fin n) (j : {j : Fin n // i ≠ j}) :
    stableScoreRowLaw d i (scoreRowSuccessorEvent d i j) ≤ stableScoreRowLaw d i univ *
      ENNReal.ofReal ((1 + coexposureSuccessorPerturbation n) *
        ((diagonalPairAt d j.val).2 / ∑ k, (diagonalPairAt d k).2)) := by
  have hsum := diagonal_competitor_sum (diagonalFemale d) i j
  have harc := diagonal_arc_bound hg (fun k ↦ (hx k).1) (fun k ↦ (hy k).1) hA hB hδ i j.val
  have hsum_pos : 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j},
      (diagonalPairAt d k.val.val).2 := by
    change 0 < ∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val
    rw [hsum]
    exact harc.1
  refine (stableScoreRowLaw_successor_le d i j (hx i) hy hsum_pos).trans ?_
  gcongr
  change diagonalFemale d j.val / ((1 - diagonalMale d i * diagonalFemale d j.val) *
    (∑ k : {k : {k : Fin n // i ≠ k} // k ≠ j}, diagonalFemale d k.val.val)) ≤ _
  rw [hsum]
  exact harc.2

end LennonPittelFormalization
