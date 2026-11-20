module

public import LennonPittel.CommonForwardCycleMoments
public import Mathlib.Probability.Independence.Integration

/-!
# Conditional occurrence of unqueried cycles

A cycle uses only its own source rows. A signed transcript of cycle tests can
therefore remove failed tests meeting a fresh target cycle before applying
independence. The transcript is the full conjunction of its signed tests.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The occurrence indicator of a prescribed cycle. -/
noncomputable def forwardCycleIndicator (σ : Equiv.Perm ι) : (ι → Option ι) → ℝ := by
  classical
  exact (forwardCycleEvent σ).indicator 1

/-- The full event described by successful and failed cycle queries. -/
def signedCycleTranscript (P N : Finset (Equiv.Perm ι)) : Set (ι → Option ι) :=
  {f | (∀ σ ∈ P, RealizesDirectedCycle f σ) ∧
    ∀ σ ∈ N, ¬RealizesDirectedCycle f σ}

/-- Disjoint cycle tests depend only on source rows outside the target support. -/
theorem realizesDirectedCycle_congr_outside {σ τ : Equiv.Perm ι}
    (hd : Disjoint σ.support τ.support) {f g : ι → Option ι}
    (hfg : ∀ i ∉ σ.support, f i = g i) :
    RealizesDirectedCycle f τ ↔ RealizesDirectedCycle g τ := by
  have hout (i : ι) (hi : i ∈ τ.support) : i ∉ σ.support :=
    fun his ↦ Finset.disjoint_left.mp hd his hi
  constructor
  · rintro ⟨hc, ha⟩
    exact ⟨hc, fun i hi ↦ (hfg i (hout i hi)).symm.trans (ha i hi)⟩
  · rintro ⟨hc, ha⟩
    exact ⟨hc, fun i hi ↦ (hfg i (hout i hi)).trans (ha i hi)⟩

/-- A transcript of tests disjoint from the target uses only outside rows. -/
theorem signedCycleTranscript_congr_outside {σ : Equiv.Perm ι}
    {P N : Finset (Equiv.Perm ι)}
    (hP : ∀ τ ∈ P, Disjoint σ.support τ.support)
    (hN : ∀ τ ∈ N, Disjoint σ.support τ.support)
    {f g : ι → Option ι} (hfg : ∀ i ∉ σ.support, f i = g i) :
    f ∈ signedCycleTranscript P N ↔ g ∈ signedCycleTranscript P N := by
  simp only [signedCycleTranscript, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hp, hn⟩
    exact ⟨fun τ ht ↦ (realizesDirectedCycle_congr_outside (hP τ ht) hfg).mp (hp τ ht),
      fun τ ht hc ↦ hn τ ht ((realizesDirectedCycle_congr_outside (hN τ ht) hfg).mpr hc)⟩
  · rintro ⟨hp, hn⟩
    exact ⟨fun τ ht ↦ (realizesDirectedCycle_congr_outside (hP τ ht) hfg).mpr (hp τ ht),
      fun τ ht hc ↦ hn τ ht ((realizesDirectedCycle_congr_outside (hN τ ht) hfg).mp hc)⟩

/-- Dropping failed tests that meet the target weakens a signed transcript. -/
theorem signedCycleTranscript_subset_trim (σ : Equiv.Perm ι)
    (P N : Finset (Equiv.Perm ι)) :
    signedCycleTranscript P N ⊆
      signedCycleTranscript P (N.filter fun τ ↦ Disjoint σ.support τ.support) := by
  intro f hf
  exact ⟨hf.1, fun τ ht ↦ hf.2 τ (Finset.mem_filter.mp ht).1⟩

/-- On an unfailed target, failed tests meeting it are automatic. -/
theorem forwardCycleEvent_inter_signedCycleTranscript_trim {σ : Equiv.Perm ι}
    (P N : Finset (Equiv.Perm ι)) (hσN : σ ∉ N) :
    forwardCycleEvent σ ∩ signedCycleTranscript P N =
      forwardCycleEvent σ ∩
        signedCycleTranscript P (N.filter fun τ ↦ Disjoint σ.support τ.support) := by
  ext f
  constructor
  · rintro ⟨hc, hh⟩
    exact ⟨hc, signedCycleTranscript_subset_trim σ P N hh⟩
  · rintro ⟨hc, hp, hn⟩
    refine ⟨hc, hp, fun τ ht hτ ↦ ?_⟩
    have hne : σ ≠ τ := fun heq ↦ hσN (heq ▸ ht)
    exact hn τ (Finset.mem_filter.mpr ⟨ht, hc.disjoint_support hτ hne⟩) hτ
lemma signedCycleTranscript_indicator_eq_of_outside {σ : Equiv.Perm ι}
    {P N : Finset (Equiv.Perm ι)}
    (hP : ∀ τ ∈ P, Disjoint σ.support τ.support)
    (hN : ∀ τ ∈ N, Disjoint σ.support τ.support)
    (f g : ι → Option ι) (hfg : ∀ i ∉ σ.support, f i = g i) :
    (signedCycleTranscript P N).indicator (1 : (ι → Option ι) → ℝ) f =
      (signedCycleTranscript P N).indicator 1 g := by
  classical
  simp only [Set.indicator_apply, Pi.one_apply,
    signedCycleTranscript_congr_outside hP hN hfg]

section IndependentRows

variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]
  (ν : ι → Measure (Option ι)) [∀ i, IsProbabilityMeasure (ν i)]

/-- A prescribed-cycle indicator is independent of any function of the other rows. -/
theorem indepFun_forwardCycleIndicator_of_outside (σ : Equiv.Perm ι)
    (g : (ι → Option ι) → ℝ)
    (hg : ∀ f h : ι → Option ι, (∀ i ∉ σ.support, f i = h i) → g f = g h) :
    IndepFun (forwardCycleIndicator σ) g (Measure.pi ν) := by
  classical
  let inside (u : σ.support → Option ι) : ι → Option ι :=
    fun i ↦ if hi : i ∈ σ.support then u ⟨i, hi⟩ else none
  let outside (u : ↥(σ.supportᶜ) → Option ι) : ι → Option ι :=
    fun i ↦ if hi : i ∈ σ.supportᶜ then u ⟨i, hi⟩ else none
  let φ (u : σ.support → Option ι) : ℝ := forwardCycleIndicator σ (inside u)
  let ψ (u : ↥(σ.supportᶜ) → Option ι) : ℝ := g (outside u)
  have hrows : iIndepFun (fun i (f : ι → Option ι) ↦ f i) (Measure.pi ν) :=
    iIndepFun_pi (fun _ ↦ aemeasurable_id)
  have hind := hrows.indepFun_finset σ.support σ.supportᶜ disjoint_compl_right
    (fun i ↦ measurable_pi_apply i)
  have hcomp := hind.comp (measurable_of_finite φ) (measurable_of_finite ψ)
  have hφ : (φ ∘ fun (f : ι → Option ι) (i : σ.support) ↦ f i) =
      forwardCycleIndicator σ := by
    funext f
    have hmem : inside (fun (i : σ.support) ↦ f i) ∈ forwardCycleEvent σ ↔
        f ∈ forwardCycleEvent σ := by
      simp only [forwardCycleEvent, RealizesDirectedCycle, Set.mem_ofPred_eq]
      constructor
      · rintro ⟨hc, ha⟩
        exact ⟨hc, fun i hi ↦ by simpa only [inside, dite_eq_left hi] using ha i hi⟩
      · rintro ⟨hc, ha⟩
        exact ⟨hc, fun i hi ↦ by simpa only [inside, dite_eq_left hi] using ha i hi⟩
    simp only [Function.comp_apply, φ, forwardCycleIndicator, Set.indicator_apply, hmem,
      Pi.one_apply]
  have hψ : (ψ ∘ fun (f : ι → Option ι) (i : ↥(σ.supportᶜ)) ↦ f i) = g := by
    funext f
    change g (outside (fun (i : ↥(σ.supportᶜ)) ↦ f i)) = g f
    apply hg
    intro i hi
    simp only [outside, dite_eq_left (Finset.mem_compl.mpr hi)]
  rw [hφ, hψ] at hcomp
  exact hcomp

/-- Integrating a cycle indicator against a function of the other rows factors. -/
theorem integral_forwardCycleIndicator_mul_of_outside (σ : Equiv.Perm ι)
    (g : (ι → Option ι) → ℝ)
    (hg : ∀ f h : ι → Option ι, (∀ i ∉ σ.support, f i = h i) → g f = g h) :
    (∫ f, forwardCycleIndicator σ f * g f ∂Measure.pi ν) =
      (Measure.pi ν).real (forwardCycleEvent σ) * ∫ f, g f ∂Measure.pi ν := by
  have hind := indepFun_forwardCycleIndicator_of_outside ν σ g hg
  have h := hind.integral_mul_eq_mul_integral
    (measurable_of_finite (forwardCycleIndicator σ)).aestronglyMeasurable
    (measurable_of_finite g).aestronglyMeasurable
  simpa only [Pi.mul_apply, forwardCycleIndicator, integral_indicator_one
    (MeasurableSet.of_discrete : MeasurableSet (forwardCycleEvent σ))] using h

/-- A cycle event factors from every event determined by the other source rows. -/
theorem measureReal_inter_forwardCycleEvent_of_outside (σ : Equiv.Perm ι)
    (E : Set (ι → Option ι))
    (hE : ∀ f h : ι → Option ι, (∀ i ∉ σ.support, f i = h i) → (f ∈ E ↔ h ∈ E)) :
    (Measure.pi ν).real (forwardCycleEvent σ ∩ E) =
      (Measure.pi ν).real (forwardCycleEvent σ) * (Measure.pi ν).real E := by
  classical
  have h := integral_forwardCycleIndicator_mul_of_outside ν σ (E.indicator 1) (by
    intro f h heq
    simp only [Set.indicator_apply, hE f h heq, Pi.one_apply])
  have hfun : (fun f ↦ forwardCycleIndicator σ f * E.indicator (1 : (ι → Option ι) → ℝ) f) =
      (forwardCycleEvent σ ∩ E).indicator 1 := by
    funext f
    by_cases hC : f ∈ forwardCycleEvent σ <;> by_cases hEf : f ∈ E <;>
      simp [forwardCycleIndicator, hC, hEf]
  rw [hfun, integral_indicator_one MeasurableSet.of_discrete,
    integral_indicator_one MeasurableSet.of_discrete] at h
  exact h

/-- Failed cycle tests cannot decrease an unfailed cycle's hazard when it avoids successes. -/
theorem signedCycleTranscript_hazard (σ : Equiv.Perm ι)
    (P N : Finset (Equiv.Perm ι)) (hσN : σ ∉ N)
    (hP : ∀ τ ∈ P, Disjoint σ.support τ.support) :
    (Measure.pi ν).real (forwardCycleEvent σ) *
        (Measure.pi ν).real (signedCycleTranscript P N) ≤
      (Measure.pi ν).real (forwardCycleEvent σ ∩ signedCycleTranscript P N) := by
  rw [forwardCycleEvent_inter_signedCycleTranscript_trim P N hσN,
    measureReal_inter_forwardCycleEvent_of_outside ν σ
      (signedCycleTranscript P (N.filter fun τ ↦ Disjoint σ.support τ.support)) (by
        intro f g hfg
        exact signedCycleTranscript_congr_outside hP
          (fun τ ht ↦ (Finset.mem_filter.mp ht).2) hfg)]
  exact mul_le_mul_of_nonneg_left
    (measureReal_mono (signedCycleTranscript_subset_trim σ P N)) (measureReal_nonneg)

/-- Conditioning on a positive-mass signed transcript preserves the target's hazard floor. -/
theorem signedCycleTranscript_conditional_hazard (σ : Equiv.Perm ι)
    (P N : Finset (Equiv.Perm ι)) (hσN : σ ∉ N)
    (hP : ∀ τ ∈ P, Disjoint σ.support τ.support)
    (hH : 0 < (Measure.pi ν).real (signedCycleTranscript P N)) :
    (Measure.pi ν).real (forwardCycleEvent σ) ≤
      (Measure.pi ν).real (forwardCycleEvent σ ∩ signedCycleTranscript P N) /
        (Measure.pi ν).real (signedCycleTranscript P N) := by
  exact (le_div_iff₀ hH).mpr (signedCycleTranscript_hazard ν σ P N hσN hP)

end IndependentRows

end LennonPittelFormalization
