module

public import LennonPittel.CommonForwardCycleMoments
public import LennonPittel.PivotResidualImageGeometry
public import LennonPittel.TwoStablePairSizeSums

/-!
# Finite error budgets for the common-row short-cycle bound

A bound on each orientation size controls the number of missing common labels.
The accumulated arc error and the label loss are explicit finite hypotheses.
-/

@[expose] public section

open Set StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

/-- A bound for the male score at a regular endpoint. -/
noncomputable def backgroundMaleCeiling (n : ℕ) : ℝ :=
  16 * Real.log n / (n : ℝ) ^ (1 / 10 : ℝ)

/-- A bound for the normalized label weight at a regular endpoint. -/
noncomputable def backgroundWeightCeiling (n : ℕ) : ℝ :=
  2060 * Real.log n / n

/-- The two losses from repeated labels and labels outside the common set. -/
noncomputable def backgroundLabelBudget (n L : ℕ) : ℝ :=
  ((L.choose 2 : ℝ) + L * (2 * n / (Real.log n) ^ 3)) * backgroundWeightCeiling n

/-- The regular rectangle bounds the number of omitted labels in the common-row law. -/
theorem commonForwardLabelLoss_le_backgroundLabelBudget {n L : ℕ}
    (C : Finset (Fin n)) (p : Fin n → ℝ)
    (hC : (Cᶜ.card : ℝ) ≤ 2 * n / (Real.log n) ^ 3)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    (hP : ∀ i, p i ≤ backgroundWeightCeiling n) :
    commonForwardLabelLoss C p L ≤ backgroundLabelBudget n L := by
  have hP₀ : 0 ≤ backgroundWeightCeiling n := by unfold backgroundWeightCeiling; positivity
  exact (commonForwardLabelLoss_le_of_weight_le C p L hp hp₁ hP).trans
    (mul_le_mul_of_nonneg_right
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg L))) hP₀)

/-- Finite hypotheses for the short-cycle estimate on rows shared by both matchings. -/
structure BackgroundCycleBudget (n L : ℕ) : Prop where
  cutoff_two : 2 ≤ L
  log_cutoff : 100 ≤ Real.log (L : ℝ)
  arc : ∀ Y : ℝ, (n : ℝ) ^ (1 / 10 : ℝ) ≤ Y →
    (L : ℝ) * (backgroundMaleCeiling n + 1 / Y) ≤ 1 / 100
  label : backgroundLabelBudget n L ≤ 1 / 100

/-- The complement of the common labels is the relative permutation's support. -/
theorem commonLabels_compl_eq_relative_support {n : ℕ} (μ ν : Matching n) :
    (Finset.univ.filter fun i : Fin n ↦ μ i = ν i)ᶜ =
      (relativeMenPermutation μ ν).support := by
  classical
  ext i
  simp [relativeMenPermutation, Equiv.Perm.mem_support, Equiv.symm_apply_eq]

end LennonPittelFormalization
