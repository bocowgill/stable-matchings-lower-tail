module

public import LennonPittel.CoexposureScoreRow

/-!
# Winning a row against competitors with bounded eligibility probabilities

If each competitor is eligible with probability at most `b`, Bernoulli's inequality
bounds the product of the losing probabilities below by one real power. Integrating
gives both the exponential endpoint estimate and the reciprocal bound at `b = 1`.
-/

@[expose] public section

open Set
open scoped BigOperators

namespace LennonPittelFormalization

variable {ι : Type*} {J : Finset ι} {a : ι → ℝ} {A b : ℝ}

/-- Exact integral of the power minorant on the unit score interval. -/
private theorem rowCompetition_integral_rpow (hb : 0 < b) (hA : 0 ≤ A) :
    (∫ z in (0 : ℝ)..1, (1 - b * z) ^ (A / b)) =
      (1 - (1 - b) ^ (1 + A / b)) / (A + b) := by
  have hr : 0 ≤ A / b := div_nonneg hA hb.le
  have h := intervalIntegral.mul_integral_comp_sub_mul (a := 0) (b := 1)
    (f := fun x : ℝ ↦ x ^ (A / b)) b 1
  simp only [mul_one, mul_zero, sub_zero] at h
  rw [integral_rpow (Or.inl (by linarith : -1 < A / b)), Real.one_rpow,
    add_comm (A / b) 1] at h
  apply (eq_div_iff (by positivity : A + b ≠ 0)).2
  have h' := (eq_div_iff (by positivity : 1 + A / b ≠ 0)).1 h
  rw [show A + b = b * (1 + A / b) by field_simp; ring]
  linear_combination h'

/-- The endpoint correction is at most exponential in the total competitor mass. -/
private theorem rowCompetition_endpoint_le_exp (hb : 0 < b) (hb₁ : b ≤ 1) (hA : 0 ≤ A) :
    (1 - b) ^ (1 + A / b) ≤ Real.exp (-A) := by
  have hr : 0 ≤ 1 + A / b := by positivity
  calc
    (1 - b) ^ (1 + A / b) ≤ Real.exp (-b) ^ (1 + A / b) :=
      Real.rpow_le_rpow (sub_nonneg.mpr hb₁) (by linarith [Real.add_one_le_exp (-b)]) hr
    _ = Real.exp (-b * (1 + A / b)) := (Real.exp_mul ..).symm
    _ ≤ Real.exp (-A) := by
      apply Real.exp_le_exp.mpr
      rw [show -b * (1 + A / b) = -b - A by field_simp; ring]
      linarith

/-- The exact endpoint correction for the power minorant of a row. -/
theorem scoreRowMass_lower_power (hb : 0 < b) (hb1 : b ≤ 1)
    (ha : ∀ j ∈ J, a j ∈ Icc 0 b) (hsum : ∑ j ∈ J, a j ≤ A) :
    (1 - (1 - b) ^ (1 + A / b)) / (A + b) ≤ scoreRowMass J a 0 1 := by
  have hA := (Finset.sum_nonneg fun j hj ↦ (ha j hj).1).trans hsum
  have hcont : Continuous fun t : ℝ ↦ (1 - b * t) ^ (A / b) :=
    (continuous_const.sub (continuous_const.mul continuous_id)).rpow_const
      fun _ ↦ Or.inr (div_nonneg hA hb.le)
  rw [← rowCompetition_integral_rpow hb hA]
  refine intervalIntegral.integral_mono_on (by norm_num) (hcont.intervalIntegrable _ _)
    ((continuous_scoreRowKernel J a).intervalIntegrable _ _) fun t ht ↦ ?_
  have hbt : b * t ≤ 1 := (mul_le_of_le_one_left ht.1 hb1).trans ht.2
  have hbase := sub_nonneg.mpr hbt
  have hweight (j) (hj : j ∈ J) : 0 ≤ a j / b := div_nonneg (ha j hj).1 hb.le
  calc
    (1 - b * t) ^ (A / b) ≤ (1 - b * t) ^ ((∑ j ∈ J, a j) / b) :=
      Real.rpow_le_rpow_of_exponent_ge' hbase (sub_le_self _ (mul_nonneg hb.le ht.1))
        (div_nonneg (Finset.sum_nonneg fun j hj ↦ (ha j hj).1) hb.le)
        (div_le_div_of_nonneg_right hsum hb.le)
    _ = ∏ j ∈ J, (1 - b * t) ^ (a j / b) := by
      rw [Finset.sum_div, Real.rpow_sum_of_nonneg hbase hweight]
    _ ≤ scoreRowKernel J a t := by
      refine Finset.prod_le_prod₀ (fun j _ ↦ Real.rpow_nonneg hbase _) fun j hj ↦ ?_
      have h := rpow_one_add_le_one_add_mul_self (s := -(b * t)) (by linarith only [hbt])
        (hweight j hj) ((div_le_one hb).mpr (ha j hj).2)
      rw [← sub_eq_add_neg] at h
      convert h using 1
      field_simp
      ring

/-- Exponential endpoint bound for competitors with a common eligibility ceiling. -/
theorem scoreRowMass_lower_bounded (hb : 0 < b) (hb1 : b ≤ 1)
    (ha : ∀ j ∈ J, a j ∈ Icc 0 b) (hA : 0 < A) (hsum : ∑ j ∈ J, a j ≤ A) :
    (1 - Real.exp (-A)) / (A + b) ≤ scoreRowMass J a 0 1 :=
  (div_le_div_of_nonneg_right (sub_le_sub_left (rowCompetition_endpoint_le_exp hb hb1 hA.le) 1)
    (add_nonneg hA.le hb.le)).trans (scoreRowMass_lower_power hb hb1 ha hsum)

/-- With eligibility bounded by one, the endpoint vanishes, including for an empty row. -/
theorem scoreRowMass_lower_reciprocal (ha : ∀ j ∈ J, a j ∈ Icc 0 1)
    (hsum : ∑ j ∈ J, a j ≤ A) :
    1 / (1 + A) ≤ scoreRowMass J a 0 1 := by
  have hA := (Finset.sum_nonneg fun j hj ↦ (ha j hj).1).trans hsum
  simpa [Real.zero_rpow (by linarith only [hA] : 1 + A ≠ 0), add_comm A 1] using
    scoreRowMass_lower_power zero_lt_one le_rfl ha hsum

end LennonPittelFormalization
