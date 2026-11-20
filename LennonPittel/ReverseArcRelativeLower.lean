module

public import LennonPittel.PivotReverseScoreSuccessor
public import LennonPittel.RowCompetition

/-!
# Lower bounds on available reverse successors

In an inactive column, the sum of competing weights is at most the total male
spouse score. The reciprocal row integral gives a common loss for every
available target.
-/

@[expose] public section

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

/-- The competing thresholds are a subcollection of the total male spouse scores,
with no duplication of the male indices. -/
theorem forwardInactiveCompetitor_sum_le_total {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i : Fin n)
    (q : ForwardInactiveColumnIndex flag i) (hx : ∀ j, 0 ≤ (diagonalPairAt d j).1) :
    (∑ k : {k : ForwardInactiveColumnIndex flag i // k ≠ q},
      (diagonalPairAt d k.val.val.val.val.1).1) ≤ ∑ j, (diagonalPairAt d j).1 := by
  classical
  let label (k : {k : ForwardInactiveColumnIndex flag i // k ≠ q}) : Fin n :=
    k.val.val.val.val.1
  have hinj : Function.Injective label := fun k l h ↦
    Subtype.ext (Subtype.ext (Subtype.ext (Subtype.ext
      (Prod.ext h (k.val.property.trans l.val.property.symm)))))
  calc
    _ = ∑ j ∈ Finset.univ.image label, (diagonalPairAt d j).1 :=
      (Finset.sum_image fun _ _ _ _ h ↦ hinj h).symm
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (fun j _ _ ↦ hx j)

/-- Relative loss for an available target when the total male spouse score is `X`. -/
noncomputable def reverseLowerArcError (X : ℝ) : ℝ := 1 / (1 + X)

theorem reverseLowerArcError_mem_Icc {X : ℝ} (hX : 0 ≤ X) :
    reverseLowerArcError X ∈ Icc 0 1 := by
  unfold reverseLowerArcError
  exact ⟨by positivity, (div_le_one (by positivity)).mpr (by linarith)⟩

/-- An available target of weight `x` has arc probability at least `x / (1 + X)`. -/
theorem normalizedForwardInactiveColumnLaw_reverseArc_ge {n : ℕ} (d : DiagonalScorePairs n)
    (flag : OffDiagonalCellIndex n → Bool) (i j : Fin n)
    (q : ForwardInactiveColumnIndex flag i) (hq : q.val.val.val.1 = j)
    (hy0 : 0 ≤ (diagonalPairAt d i).2) (hy1 : (diagonalPairAt d i).2 < 1)
    (hx : ∀ k, (diagonalPairAt d k).1 ∈ Icc 0 1) :
    let X := ∑ k, (diagonalPairAt d k).1
    0 < X → ENNReal.ofReal (1 - reverseLowerArcError X) *
      ENNReal.ofReal ((diagonalPairAt d j).1 / X) ≤
      normalizedForwardInactiveColumnLaw d flag i (forwardInactiveReverseArcEvent d flag i j) := by
  intro X hX
  let v (k : ForwardInactiveColumnIndex flag i) := (diagonalPairAt d k.val.val.val.1).1
  let y := (diagonalPairAt d i).2
  have hsub := forwardInactiveCompetitor_sum_le_total d flag i q (fun k ↦ (hx k).1)
  have hrow := scoreRowMass_lower_reciprocal (J := Finset.univ)
    (a := fun k : {k : ForwardInactiveColumnIndex flag i // k ≠ q} ↦ v k.val)
    (A := X) (fun k _ ↦ hx k.val.val.val.val.1) hsub
  have hv : v q = (diagonalPairAt d j).1 := by dsimp [v]; rw [hq]
  have hmass := reverseSuccessorColumnEvent_mass (v := v) q hy0 hy1 (fun k ↦ hx k.val.val.val.1)
  have hδ := (reverseLowerArcError_mem_Icc hX.le).2
  refine le_trans ?_ (measure_mono (subset_iUnion (fun s :
    {s : ForwardInactiveColumnIndex flag i // s.val.val.val.1 = j} ↦
      reverseSuccessorColumnEvent y v s.val) ⟨q, hq⟩))
  change _ ≤ (Measure.pi fun _ : ForwardInactiveColumnIndex flag i ↦
    unitScoreLaw.prod (inactiveFemaleScoreLaw y)) (reverseSuccessorColumnEvent y v q)
  rw [hmass, ← ENNReal.ofReal_mul (sub_nonneg.mpr hδ)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ = v q * (1 / (1 + X)) := by
      rw [hv, reverseLowerArcError]
      field_simp [hX.ne', show 1 + X ≠ 0 by positivity]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hrow (hx _).1

end LennonPittelFormalization
