module

public import Mathlib.Probability.Moments.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Tactic.FunProp
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# Lower tails from a cycle-count Laplace estimate

The independent-row cycle argument supplies the Laplace bound. These generic
lemmas turn that bound into a Chernoff lower tail and the numerical bound
used by the existing background-cycle estimate.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace LennonPittelFormalization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]

/-- A nonnegative count has an integrable negative exponential under a finite measure. -/
theorem integrable_exp_neg_mul_count {N : Ω → ℕ} (hN : Measurable N)
    {t : ℝ} (ht : 0 ≤ t) :
    Integrable (fun x ↦ Real.exp (-t * (N x : ℝ))) μ := by
  apply (integrable_const (1 : ℝ)).mono'
  · fun_prop
  · filter_upwards [] with x
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ht) (Nat.cast_nonneg _)

/-- A single Laplace estimate controls a lower tail at an arbitrary real threshold. -/
theorem measure_le_of_cycle_laplace {X : Ω → ℝ} {t b m : ℝ} (ht : 0 ≤ t)
    (hint : Integrable (fun x ↦ Real.exp (-t * X x)) μ)
    (hlap : (∫ x, Real.exp (-t * X x) ∂μ) ≤ Real.exp ((Real.exp (-t) - 1) * m)) :
    μ.real {x | X x ≤ b} ≤ Real.exp (t * b + (Real.exp (-t) - 1) * m) := by
  have h := measure_le_le_exp_mul_mgf (μ := μ) (X := X) (t := -t) b
    (neg_nonpos.mpr ht) hint
  calc
    _ ≤ Real.exp (t * b) * (∫ x, Real.exp (-t * X x) ∂μ) := by
      simpa only [mgf, neg_neg] using h
    _ ≤ Real.exp (t * b) * Real.exp ((Real.exp (-t) - 1) * m) :=
      mul_le_mul_of_nonneg_left hlap (Real.exp_nonneg _)
    _ = _ := (Real.exp_add _ _).symm

/-- The Poisson-form Chernoff lower tail follows from a count's Laplace estimates. -/
theorem measure_le_chernoff_of_cycle_laplace {X : Ω → ℝ} {m a : ℝ}
    (ha : 0 < a) (ha' : a < 1)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x ↦ Real.exp (-t * X x)) μ)
    (hlap : ∀ t : ℝ, 0 ≤ t →
      (∫ x, Real.exp (-t * X x) ∂μ) ≤ Real.exp ((Real.exp (-t) - 1) * m)) :
    μ.real {x | X x ≤ a * m} ≤ Real.exp (-m * (1 - a + a * Real.log a)) := by
  have ht : 0 ≤ -Real.log a := (neg_pos.mpr (Real.log_neg ha ha')).le
  have h := measure_le_of_cycle_laplace ht (hint _ ht) (hlap _ ht) (b := a * m)
  rw [neg_neg, Real.exp_log ha] at h
  calc
    _ ≤ Real.exp (-Real.log a * (a * m) + (a - 1) * m) := h
    _ = _ := congrArg Real.exp (by ring)

/-- A convenient numerical exponential bound implies the previous inverse-log bound. -/
theorem exp_neg_div_1600_le_1200_div {B : ℝ} (hB : 0 < B) :
    Real.exp (-B / 1600) ≤ 1200 / B := by
  have hhalf : Real.exp (-1 : ℝ) ≤ 1 / 2 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_iff₀ (Real.exp_pos (1 : ℝ))).mpr
    nlinarith [Real.add_one_le_exp (1 : ℝ)]
  have hmul := Real.mul_exp_neg_le_exp_neg_one (B / 1600)
  have hneg : -(B / 1600) = -B / 1600 := by ring
  rw [hneg] at hmul
  apply (le_div_iff₀ hB).mpr
  nlinarith

/-- The source's `19/20` mean floor gives a uniform exponential background tail. -/
theorem measure_lt_background_of_cycle_laplace {X : Ω → ℝ} {m B : ℝ}
    (hB : 0 < B) (hmean : (19 / 20 : ℝ) * B ≤ m)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x ↦ Real.exp (-t * X x)) μ)
    (hlap : ∀ t : ℝ, 0 ≤ t →
      (∫ x, Real.exp (-t * X x) ∂μ) ≤ Real.exp ((Real.exp (-t) - 1) * m)) :
    μ.real {x | X x < (9 / 10 : ℝ) * B} ≤ Real.exp (-B / 1600) := by
  let t : ℝ := Real.log (40 / 39 : ℝ)
  have ht : 0 ≤ t := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 40 / 39)
  have ht_upper : t ≤ 1 / 39 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 40 / 39)
    norm_num at h
    exact h
  have he : Real.exp (-t) = 39 / 40 := by
    dsimp [t]
    rw [Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 40 / 39)]
    norm_num
  have h := measure_le_of_cycle_laplace ht (hint t ht) (hlap t ht)
    (b := (9 / 10 : ℝ) * B)
  have hnum : t * ((9 / 10 : ℝ) * B) + (Real.exp (-t) - 1) * m ≤ -B / 1600 := by
    rw [he]
    have htb := mul_le_mul_of_nonneg_right ht_upper (by positivity : 0 ≤ (9 / 10 : ℝ) * B)
    nlinarith
  have hsub : {x | X x < (9 / 10 : ℝ) * B} ⊆ {x | X x ≤ (9 / 10 : ℝ) * B} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    exact le_of_lt hx
  exact (measureReal_mono hsub).trans (h.trans (Real.exp_le_exp.mpr hnum))

/-- The same Laplace estimates satisfy the old numerical background-tail interface. -/
theorem measure_lt_background_inverse_log_of_cycle_laplace {X : Ω → ℝ} {m B : ℝ}
    (hB : 0 < B) (hmean : (19 / 20 : ℝ) * B ≤ m)
    (hint : ∀ t : ℝ, 0 ≤ t → Integrable (fun x ↦ Real.exp (-t * X x)) μ)
    (hlap : ∀ t : ℝ, 0 ≤ t →
      (∫ x, Real.exp (-t * X x) ∂μ) ≤ Real.exp ((Real.exp (-t) - 1) * m)) :
    μ.real {x | X x < (9 / 10 : ℝ) * B} ≤ 1200 / B :=
  (measure_lt_background_of_cycle_laplace hB hmean hint hlap).trans
    (exp_neg_div_1600_le_1200_div hB)

end LennonPittelFormalization
