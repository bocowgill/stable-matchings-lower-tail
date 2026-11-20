module

public import LennonPittel.CoexposureGoodScores
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Volume bounds for spouse-score shells

Nonnegative spouse scores with sum at most a given radius form a simplex.
A lower bound on one coordinate translates that simplex to a smaller one.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal BigOperators Topology
namespace LennonPittelFormalization

/-- Nonnegative arrays whose coordinate sum is at most the given radius. -/
def scoreSimplex (n : ℕ) (s : ℝ) : Set (Fin n → ℝ) :=
  {y | (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s}

/-- The simplex cut out by a nonnegative coordinate sum is measurable. -/
theorem measurableSet_scoreSimplex (n : ℕ) (s : ℝ) :
    MeasurableSet (scoreSimplex n s) := by
  unfold scoreSimplex
  rw [ofPred_and, ofPred_forall]
  exact (MeasurableSet.iInter fun i ↦ measurableSet_le measurable_const (measurable_pi_apply i)).inter
    (measurableSet_le (Finset.measurable_sum _ fun i _ ↦ measurable_pi_apply i) measurable_const)

/-- The volume of a positive-orthant simplex. -/
theorem volume_scoreSimplex (n : ℕ) {s : ℝ} (hs : 0 ≤ s) :
    volume (scoreSimplex n s) = ENNReal.ofReal (s ^ n / (n.factorial : ℝ)) := by
  induction n generalizing s with
  | zero =>
    simp [scoreSimplex, hs, volume_pi]
  | succ n ih =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) ↦ ℝ) 0
    let S : Set (ℝ × (Fin n → ℝ)) :=
      {a | 0 ≤ a.1 ∧ a.2 ∈ scoreSimplex n (s - a.1)}
    have heq : e ⁻¹' S = scoreSimplex (n + 1) s := by
      ext y
      simp only [e, MeasurableEquiv.piFinSuccAbove_apply, Fin.insertNthEquiv_symm_apply,
        Fin.removeNth, Fin.succAbove_zero, Set.mem_preimage, S, scoreSimplex, mem_ofPred_eq,
        Fin.forall_fin_succ, Fin.sum_univ_succ]
      exact ⟨fun h ↦ ⟨⟨h.1, h.2.1⟩, by linarith [h.2.2]⟩,
        fun h ↦ ⟨h.1.1, h.1.2, by linarith [h.2]⟩⟩
    have hS : MeasurableSet S :=
      e.measurableSet_preimage.mp (heq.symm ▸ measurableSet_scoreSimplex _ _)
    have he : MeasurePreserving e volume volume :=
      volume_preserving_piFinSuccAbove _ _
    rw [← heq, he.measure_preimage_emb e.measurableEmbedding]
    change ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) S = _
    rw [Measure.prod_apply hS]
    let f (t : ℝ) : ℝ := (s - t) ^ n / (n.factorial : ℝ)
    have hslice (t : ℝ) :
        volume (Prod.mk t ⁻¹' S) = (Icc 0 s).indicator (fun t ↦ ENNReal.ofReal (f t)) t := by
      by_cases ht : t ∈ Icc 0 s
      · rw [indicator_of_mem ht, ← ih (sub_nonneg.mpr ht.2)]
        congr 1
        ext y
        change (0 ≤ t ∧ y ∈ scoreSimplex n (s - t)) ↔ y ∈ scoreSimplex n (s - t)
        exact and_iff_right ht.1
      · rw [indicator_of_notMem ht]
        have hempty : Prod.mk t ⁻¹' S = ∅ := by
          apply Set.eq_empty_iff_forall_notMem.mpr
          intro y hy
          change 0 ≤ t ∧ (∀ i, 0 ≤ y i) ∧ ∑ i, y i ≤ s - t at hy
          have hsum : 0 ≤ ∑ i, y i := Finset.sum_nonneg fun i _ ↦ hy.2.1 i
          exact ht ⟨hy.1, by linarith [hy.2.2]⟩
        rw [hempty, measure_empty]
    rw [lintegral_congr hslice, lintegral_indicator measurableSet_Icc]
    have hfi : IntegrableOn f (Icc 0 s) := (by fun_prop : Continuous f).integrableOn_Icc
    rw [← ofReal_integral_eq_lintegral_ofReal hfi
      ((ae_restrict_mem measurableSet_Icc).mono fun t ht ↦ by
        dsimp only [f]
        exact div_nonneg (pow_nonneg (sub_nonneg.mpr ht.2) _) (Nat.cast_nonneg _))]
    rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hs]
    congr 1
    dsimp only [f]
    rw [intervalIntegral.integral_div, intervalIntegral.integral_comp_sub_left (fun x : ℝ ↦ x ^ n) s, sub_self,
      sub_zero, integral_pow, zero_pow (by omega : n + 1 ≠ 0), sub_zero, Nat.factorial_succ,
      Nat.cast_mul, Nat.cast_succ]
    simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]

/-- Translating one coordinate reduces the radius by its lower bound. -/
theorem volume_scoreSimplex_coordinate_lower_bound (n : ℕ) (i : Fin n) {s a : ℝ}
    (ha : 0 ≤ a) (has : a ≤ s) :
    volume (scoreSimplex n s ∩ {y | a ≤ y i}) =
      ENNReal.ofReal ((s - a) ^ n / (n.factorial : ℝ)) := by
  have htrans : (fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i}) = scoreSimplex n (s - a) := by
    ext y
    simp only [mem_preimage, mem_inter_iff, scoreSimplex, mem_ofPred_eq, Pi.add_apply,
      Finset.sum_add_distrib, Finset.sum_pi_single', Finset.mem_univ, ite_true, Pi.single_eq_same]
    constructor
    · rintro ⟨⟨hy, hsum⟩, hi⟩
      refine ⟨fun j ↦ ?_, by linarith⟩
      by_cases h : j = i
      · subst j
        linarith
      · simpa only [Pi.single_eq_of_ne h, add_zero] using hy j
    · rintro ⟨hy, hsum⟩
      refine ⟨⟨fun j ↦ add_nonneg (hy j) ?_, by linarith⟩, by linarith [hy i]⟩
      by_cases h : j = i
      · subst j
        simpa only [Pi.single_eq_same] using ha
      · rw [Pi.single_eq_of_ne h]
  let v : Fin n → ℝ := Pi.single i a
  have hmeasure := (measurePreserving_add_right (volume : Measure (Fin n → ℝ))
    v).measure_preimage_emb (measurableEmbedding_addRight v)
      (scoreSimplex n s ∩ {y | a ≤ y i})
  change volume ((fun y : Fin n → ℝ ↦ y + Pi.single i a) ⁻¹'
      (scoreSimplex n s ∩ {y | a ≤ y i})) = _ at hmeasure
  rw [htrans, volume_scoreSimplex n (sub_nonneg.mpr has)] at hmeasure
  exact hmeasure.symm

/-- A large relative coordinate in a positive-score shell costs simplex volume. -/
theorem volume_scoreSimplex_shell_large_coordinate_le (n : ℕ) (i : Fin n)
    {l u a : ℝ} (hl : 0 < l) (ha : 0 ≤ a) (hau : a * l ≤ u) :
    volume {y : Fin n → ℝ | y ∈ scoreSimplex n u ∧ l ≤ ∑ j, y j ∧
      a < y i / (∑ j, y j)} ≤ ENNReal.ofReal ((u - a * l) ^ n / (n.factorial : ℝ)) := by
  rw [← volume_scoreSimplex_coordinate_lower_bound n i (mul_nonneg ha hl.le) hau]
  apply measure_mono
  intro y hy
  exact ⟨hy.1, (mul_le_mul_of_nonneg_left hy.2.1 ha).trans
    ((lt_div_iff₀ (hl.trans_le hy.2.1)).mp hy.2.2).le⟩

end LennonPittelFormalization
