module

public import LennonPittel.CycleQueryHazard

/-!
# Laplace bound for cycles of independent successor rows

Removing cycles meeting a target leaves a count determined by the outside rows.
On occurrence of the target, every other occurring cycle already lies outside.
This gives a direct insertion induction for the count's Laplace transform.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

private theorem count_mono {S T : Finset (Equiv.Perm ι)} (hST : S ⊆ T)
    (f : ι → Option ι) : realizedForwardCycleCount S f ≤ realizedForwardCycleCount T f := by
  classical
  exact Finset.card_le_card (Finset.filter_subset_filter _ hST)

private theorem count_trim {σ : Equiv.Perm ι} (S : Finset (Equiv.Perm ι))
    (hσ : σ ∉ S) {f : ι → Option ι} (hf : RealizesDirectedCycle f σ) :
    realizedForwardCycleCount (S.filter fun τ ↦ Disjoint σ.support τ.support) f =
      realizedForwardCycleCount S f := by
  classical
  unfold realizedForwardCycleCount
  congr 1
  ext τ
  simp only [Finset.mem_filter, and_assoc]
  constructor
  · tauto
  · rintro ⟨hτ, hr⟩
    exact ⟨hτ, hf.disjoint_support hr (fun he ↦ hσ (he ▸ hτ)), hr⟩

private theorem count_trim_congr {σ : Equiv.Perm ι} (S : Finset (Equiv.Perm ι))
    {f g : ι → Option ι} (hfg : ∀ i ∉ σ.support, f i = g i) :
    realizedForwardCycleCount (S.filter fun τ ↦ Disjoint σ.support τ.support) f =
      realizedForwardCycleCount (S.filter fun τ ↦ Disjoint σ.support τ.support) g := by
  classical
  unfold realizedForwardCycleCount
  congr 1
  apply Finset.filter_congr
  intro τ hτ
  exact realizesDirectedCycle_congr_outside (Finset.mem_filter.mp hτ).2 hfg

section IndependentRows

variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  (ν : ι → Measure (Option ι)) [∀ i, IsProbabilityMeasure (ν i)]

private theorem integral_indicator_mul_pow_count_ge (σ : Equiv.Perm ι)
    (S : Finset (Equiv.Perm ι)) (hσ : σ ∉ S) {z : ℝ} (hz : 0 ≤ z) (hz₁ : z ≤ 1) :
    (Measure.pi ν).real (forwardCycleEvent σ) *
        (∫ f, z ^ realizedForwardCycleCount S f ∂Measure.pi ν) ≤
      ∫ f, forwardCycleIndicator σ f * z ^ realizedForwardCycleCount S f ∂Measure.pi ν := by
  classical
  let D := S.filter fun τ ↦ Disjoint σ.support τ.support
  have hfactor := integral_forwardCycleIndicator_mul_of_outside ν σ
    (fun f ↦ z ^ realizedForwardCycleCount D f) (by
      intro f g hfg
      rw [count_trim_congr S hfg])
  have heq : (fun f ↦ forwardCycleIndicator σ f * z ^ realizedForwardCycleCount S f) =
      (fun f ↦ forwardCycleIndicator σ f * z ^ realizedForwardCycleCount D f) := by
    funext f
    by_cases hf : RealizesDirectedCycle f σ
    · rw [count_trim S hσ hf]
    · simp [forwardCycleIndicator, forwardCycleEvent, hf]
  rw [heq, hfactor]
  apply mul_le_mul_of_nonneg_left _ measureReal_nonneg
  apply integral_mono (Integrable.of_finite) (Integrable.of_finite)
  intro f
  exact pow_le_pow_of_le_one hz hz₁ (count_mono (Finset.filter_subset _ S) f)

/-- The cycle count has the Poisson Laplace upper bound at its actual mean. -/
theorem integral_pow_realizedForwardCycleCount_le (S : Finset (Equiv.Perm ι))
    {z : ℝ} (hz : 0 ≤ z) (hz₁ : z ≤ 1) :
    (∫ f, z ^ realizedForwardCycleCount S f ∂Measure.pi ν) ≤
      Real.exp ((z - 1) * ∑ σ ∈ S, (Measure.pi ν).real (forwardCycleEvent σ)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [realizedForwardCycleCount]
  | @insert σ S hσ ih =>
    let p := (Measure.pi ν).real (forwardCycleEvent σ)
    let I := ∫ f, z ^ realizedForwardCycleCount S f ∂Measure.pi ν
    have hp : 0 ≤ p := measureReal_nonneg
    have hp₁ : p ≤ 1 := measureReal_le_one
    have ha : 0 ≤ 1 - (1 - z) * p := by nlinarith
    have hins (f : ι → Option ι) :
        z ^ realizedForwardCycleCount (insert σ S) f =
          z ^ realizedForwardCycleCount S f -
            (1 - z) * (forwardCycleIndicator σ f * z ^ realizedForwardCycleCount S f) := by
      by_cases hf : RealizesDirectedCycle f σ
      · have hcount : realizedForwardCycleCount (insert σ S) f =
            realizedForwardCycleCount S f + 1 := by
          simp [realizedForwardCycleCount, Finset.filter_insert, hf, hσ]
        rw [hcount, pow_succ]
        have hmem : f ∈ forwardCycleEvent σ := hf
        simp only [forwardCycleIndicator, Set.indicator_of_mem hmem, Pi.one_apply]
        ring
      · have hcount : realizedForwardCycleCount (insert σ S) f =
            realizedForwardCycleCount S f := by
          simp [realizedForwardCycleCount, Finset.filter_insert, hf]
        simp [hcount, forwardCycleIndicator, forwardCycleEvent, hf]
    have hcross := integral_indicator_mul_pow_count_ge ν σ S hσ hz hz₁
    have hstep : (∫ f, z ^ realizedForwardCycleCount (insert σ S) f ∂Measure.pi ν) ≤
        (1 - (1 - z) * p) * I := by
      simp_rw [hins]
      rw [integral_sub (Integrable.of_finite) (Integrable.of_finite), integral_const_mul]
      dsimp [I, p] at *
      nlinarith [mul_le_mul_of_nonneg_left hcross (sub_nonneg.mpr hz₁)]
    calc
      _ ≤ (1 - (1 - z) * p) * I := hstep
      _ ≤ (1 - (1 - z) * p) *
          Real.exp ((z - 1) * ∑ τ ∈ S, (Measure.pi ν).real (forwardCycleEvent τ)) :=
        mul_le_mul_of_nonneg_left ih ha
      _ ≤ Real.exp ((z - 1) * p) *
          Real.exp ((z - 1) * ∑ τ ∈ S, (Measure.pi ν).real (forwardCycleEvent τ)) := by
        apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
        have he := Real.add_one_le_exp ((z - 1) * p)
        nlinarith
      _ = _ := by
        rw [← Real.exp_add, Finset.sum_insert hσ]
        congr 1
        dsimp [p]
        ring

/-- Negative exponential moments of the actual cycle count are at most Poisson moments. -/
theorem integral_exp_neg_mul_realizedForwardCycleCount_le (S : Finset (Equiv.Perm ι))
    {t : ℝ} (ht : 0 ≤ t) :
    (∫ f, Real.exp (-t * (realizedForwardCycleCount S f : ℝ)) ∂Measure.pi ν) ≤
      Real.exp ((Real.exp (-t) - 1) *
        (∫ f, (realizedForwardCycleCount S f : ℝ) ∂Measure.pi ν)) := by
  have hz : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht)
  have h := integral_pow_realizedForwardCycleCount_le ν S (Real.exp_pos _).le hz
  rw [integral_realizedForwardCycleCount] at *
  simpa only [← Real.exp_nat_mul, mul_comm] using h

end IndependentRows

end LennonPittelFormalization
