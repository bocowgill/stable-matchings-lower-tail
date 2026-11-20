module

public import LennonPittel.PivotTwoCycleForest
public import LennonPittel.ReverseIIDLabelGood
public import Mathlib.NumberTheory.Harmonic.Bounds
public import Mathlib.Probability.Moments.Variance

/-!
# Short cycles of independent forward rows

A directed cycle specifies one outgoing arrow on each of its vertices.
Disjoint cycles use independent rows, and intersecting distinct cycles
cannot both occur. Consequently the cycle count has variance at most
its mean, including when we restrict the allowed labels and lengths.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace LennonPittelFormalization

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The candidate cycles with support contained in the common labels and length in `K`. -/
noncomputable def commonForwardCycles (C : Finset ι) (K : Finset ℕ) :
    Finset (Equiv.Perm ι) := by
  classical
  exact Finset.univ.filter fun σ ↦ σ.IsCycle ∧ σ.support ⊆ C ∧ σ.support.card ∈ K

theorem mem_commonForwardCycles {C : Finset ι} {K : Finset ℕ} {σ : Equiv.Perm ι} :
    σ ∈ commonForwardCycles C K ↔ σ.IsCycle ∧ σ.support ⊆ C ∧ σ.support.card ∈ K := by
  classical
  simp [commonForwardCycles]

/-- Count the realized cycles among the candidates in a fixed finite set. -/
noncomputable def realizedForwardCycleCount (S : Finset (Equiv.Perm ι)) (f : ι → Option ι) :
    ℕ := by
  classical
  exact (S.filter (RealizesDirectedCycle f)).card

/-- The number of realized cycles of lengths two through `L` using only common labels. -/
noncomputable def commonForwardCycleCount (C : Finset ι) (L : ℕ) (f : ι → Option ι) :
    ℕ :=
  realizedForwardCycleCount (commonForwardCycles C (Finset.Icc 2 L)) f

/-- The event that a prescribed cycle is realized by the outcome rows. -/
def forwardCycleEvent (σ : Equiv.Perm ι) : Set (ι → Option ι) :=
  {f | RealizesDirectedCycle f σ}

section RowLaws

variable [MeasurableSpace (Option ι)]

private theorem measureReal_pi_prescribed (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (s : Finset ι) (a : ι → Option ι) :
    (Measure.pi ν).real {f | ∀ i ∈ s, f i = a i} = ∏ i ∈ s, (ν i).real {a i} := by
  let B (i : ι) : Set (Option ι) := if i ∈ s then {a i} else univ
  have hB : {f | ∀ i ∈ s, f i = a i} = univ.pi B := by
    ext f
    simp only [Set.mem_ofPred_eq, Set.mem_univ_pi]
    constructor
    · intro h i
      by_cases hi : i ∈ s <;> simp [B, hi, h]
    · intro h i hi
      simpa [B, hi] using h i
  rw [hB, measureReal_def, Measure.pi_pi, ENNReal.toReal_prod]
  have hp (i : ι) : ((ν i) (B i)).toReal = if i ∈ s then (ν i).real {a i} else 1 := by
    by_cases hi : i ∈ s <;> simp [B, hi, measureReal_def]
  simp_rw [hp]
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- The probability of realizing a prescribed cycle is the product of its arc probabilities. -/
theorem measureReal_forwardCycleEvent (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] {σ : Equiv.Perm ι} (hσ : σ.IsCycle) :
    (Measure.pi ν).real (forwardCycleEvent σ) = ∏ i ∈ σ.support, (ν i).real {some (σ i)} := by
  simp only [forwardCycleEvent, RealizesDirectedCycle, hσ, true_and]
  exact measureReal_pi_prescribed ν _ _

/-- For distinct cycles, joint probability is no greater than the product of their probabilities. -/
theorem measureReal_inter_forwardCycleEvent_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] {σ τ : Equiv.Perm ι} (hσ : σ.IsCycle)
    (hτ : τ.IsCycle) (hne : σ ≠ τ) :
    (Measure.pi ν).real (forwardCycleEvent σ ∩ forwardCycleEvent τ) ≤
      (Measure.pi ν).real (forwardCycleEvent σ) * (Measure.pi ν).real (forwardCycleEvent τ) := by
  classical
  by_cases hd : Disjoint σ.support τ.support
  · let a (i : ι) := if i ∈ σ.support then some (σ i) else some (τ i)
    have he : forwardCycleEvent σ ∩ forwardCycleEvent τ =
        {f | ∀ i ∈ σ.support ∪ τ.support, f i = a i} := by
      ext f
      simp only [Set.mem_inter_iff, forwardCycleEvent, Set.mem_ofPred_eq, RealizesDirectedCycle,
        hσ, hτ, true_and]
      constructor
      · rintro ⟨hs, ht⟩ i hi
        by_cases hs' : i ∈ σ.support
        · simpa only [a, ite_eq_left hs'] using hs i hs'
        · simpa only [a, ite_eq_right hs'] using ht i ((Finset.mem_union.mp hi).resolve_left hs')
      · intro h
        exact ⟨fun i hi ↦ by simpa only [a, ite_eq_left hi] using h i (Finset.mem_union_left _ hi),
          fun i hi ↦ by
            have hnot := fun hmem ↦ Finset.disjoint_left.mp hd hmem hi
            simpa only [a, ite_eq_right hnot] using h i (Finset.mem_union_right _ hi)⟩
    rw [he, measureReal_pi_prescribed, Finset.prod_union hd,
      measureReal_forwardCycleEvent ν hσ, measureReal_forwardCycleEvent ν hτ]
    refine le_of_eq (congrArg₂ (· * ·) ?_ ?_)
    · exact Finset.prod_congr rfl fun i hi ↦ by simp only [a, ite_eq_left hi]
    · exact Finset.prod_congr rfl fun i hi ↦ by
        simp only [a, ite_eq_right (show i ∉ σ.support from fun h ↦ Finset.disjoint_left.mp hd h hi)]
  · have he : forwardCycleEvent σ ∩ forwardCycleEvent τ = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.mpr fun f hf ↦ hd ?_
      exact hf.1.disjoint_support hf.2 hne
    rw [he, measureReal_empty]
    exact mul_nonneg measureReal_nonneg measureReal_nonneg

private noncomputable def cycleIndicator (σ : Equiv.Perm ι) (f : ι → Option ι) : ℝ :=
  (forwardCycleEvent σ).indicator (1 : (ι → Option ι) → ℝ) f

omit [MeasurableSpace (Option ι)] in
private theorem count_eq_sum_cycleIndicator (S : Finset (Equiv.Perm ι)) :
    (fun f ↦ (realizedForwardCycleCount S f : ℝ)) =
      fun f ↦ ∑ σ ∈ S, cycleIndicator σ f := by
  classical
  funext f
  simp only [realizedForwardCycleCount, cycleIndicator, Set.indicator_apply, forwardCycleEvent,
    Set.mem_ofPred_eq, Pi.one_apply, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]

variable [MeasurableSingletonClass (Option ι)]

private theorem cycleIndicator_memLp (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (σ : Equiv.Perm ι) : MemLp (cycleIndicator σ) 2 ν :=
  memLp_indicator_const 2
    (MeasurableSet.of_discrete : MeasurableSet (forwardCycleEvent σ)).nullMeasurableSet
    (1 : ℝ) (Or.inr (measure_ne_top _ _))

theorem realizedForwardCycleCount_memLp (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (S : Finset (Equiv.Perm ι)) :
    MemLp (fun f ↦ (realizedForwardCycleCount S f : ℝ)) 2 ν := by
  rw [count_eq_sum_cycleIndicator]
  simpa only [← Finset.sum_apply] using memLp_finsetSum' S fun σ _ ↦ cycleIndicator_memLp ν σ

/-- The expected cycle count is the sum of the individual cycle probabilities. -/
theorem integral_realizedForwardCycleCount (ν : Measure (ι → Option ι)) [IsFiniteMeasure ν]
    (S : Finset (Equiv.Perm ι)) :
    (∫ f, (realizedForwardCycleCount S f : ℝ) ∂ν) =
      ∑ σ ∈ S, ν.real (forwardCycleEvent σ) := by
  rw [count_eq_sum_cycleIndicator]
  rw [integral_finsetSum _ fun σ _ ↦ (cycleIndicator_memLp ν σ).integrable (by simp)]
  exact Finset.sum_congr rfl fun σ _ ↦ integral_indicator_one MeasurableSet.of_discrete

omit [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] in
private theorem cycleIndicator_mul_eq_indicator (σ τ : Equiv.Perm ι) :
    cycleIndicator σ * cycleIndicator τ =
      (forwardCycleEvent σ ∩ forwardCycleEvent τ).indicator (1 : (ι → Option ι) → ℝ) := by
  classical
  funext f
  by_cases hσ : f ∈ forwardCycleEvent σ <;> by_cases hτ : f ∈ forwardCycleEvent τ <;>
    simp [cycleIndicator, hσ, hτ]

/-- Disjoint row sets give independent cycle tests. Distinct intersecting
cycles are mutually exclusive. These facts bound the variance by the mean. -/
theorem variance_realizedForwardCycleCount_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (S : Finset (Equiv.Perm ι))
    (hS : ∀ σ ∈ S, σ.IsCycle) :
    Var[fun f ↦ (realizedForwardCycleCount S f : ℝ); Measure.pi ν] ≤
      ∫ f, (realizedForwardCycleCount S f : ℝ) ∂(Measure.pi ν) := by
  classical
  rw [integral_realizedForwardCycleCount, count_eq_sum_cycleIndicator,
    variance_fun_sum' (fun σ _ ↦ cycleIndicator_memLp (Measure.pi ν) σ)]
  apply Finset.sum_le_sum
  intro σ hσ
  calc
    _ ≤ ∑ τ ∈ S, if τ = σ then (Measure.pi ν).real (forwardCycleEvent σ) else 0 := by
      refine Finset.sum_le_sum fun τ hτ ↦ ?_
      rw [covariance_eq_sub (cycleIndicator_memLp (Measure.pi ν) σ)
        (cycleIndicator_memLp (Measure.pi ν) τ), cycleIndicator_mul_eq_indicator,
        integral_indicator_one MeasurableSet.of_discrete]
      simp only [cycleIndicator, integral_indicator_one MeasurableSet.of_discrete]
      by_cases he : τ = σ
      · subst τ
        simp only [Set.inter_self]
        exact sub_le_self _ (mul_nonneg measureReal_nonneg measureReal_nonneg)
      · rw [ite_eq_right he]
        exact sub_nonpos.mpr (measureReal_inter_forwardCycleEvent_le ν (hS σ hσ) (hS τ hτ)
          (Ne.symm he))
    _ = _ := by simp [hσ]

end RowLaws

section ReferenceWeights

/-- The independent samples of `k` distinct labels all lying in `C`. -/
private noncomputable def injectiveCommonLabels (C : Finset ι) (k : ℕ) :
    Finset (Fin k → ι) := by
  classical
  exact Finset.univ.filter fun x ↦ Function.Injective x ∧ ∀ i, x i ∈ C

private theorem mem_injectiveCommonLabels {C : Finset ι} {k : ℕ} {x : Fin k → ι} :
    x ∈ injectiveCommonLabels C k ↔ Function.Injective x ∧ ∀ i, x i ∈ C := by
  classical
  simp [injectiveCommonLabels]

/-- The weight of the injective samples is the elementary symmetric sum
over common labels times the number of orderings of a support. -/
private theorem sum_injectiveCommonLabels_eq (C : Finset ι) (k : ℕ) (r : ι → ℝ≥0∞) :
    (∑ x ∈ injectiveCommonLabels C k, ∏ i, r (x i)) =
      (k.factorial : ℝ≥0∞) * ∑ s ∈ C.powersetCard k, ∏ i ∈ s, r i := by
  classical
  let G := injectiveCommonLabels C k
  let supp (x : Fin k → ι) := Finset.univ.image x
  have hm (x : Fin k → ι) (hx : x ∈ G) : supp x ∈ C.powersetCard k := by
    obtain ⟨hinj, hC⟩ := mem_injectiveCommonLabels.mp hx
    refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
    · rintro i hi
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
      exact hC j
    · rw [show supp x = Finset.univ.image x from rfl,
        Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  have hcard (s : Finset ι) (hs : s ∈ C.powersetCard k) :
      (G.filter (fun x ↦ supp x = s)).card = k.factorial := by
    obtain ⟨hsC, hsk⟩ := Finset.mem_powersetCard.mp hs
    let E := G.filter (fun x ↦ supp x = s)
    let f (x : E) : Fin k ≃ s := by
      have hx := Finset.mem_filter.mp x.property
      have hxi := (mem_injectiveCommonLabels.mp hx.1).1
      let g (j : Fin k) : s := ⟨x.val j, hx.2 ▸ Finset.mem_image_of_mem x.val (Finset.mem_univ j)⟩
      exact Equiv.ofBijective g ⟨fun _ _ h ↦ hxi (congrArg Subtype.val h), fun i ↦ by
        have hi : i.val ∈ supp x.val := hx.2.symm ▸ i.property
        obtain ⟨j, -, hj⟩ := Finset.mem_image.mp hi
        exact ⟨j, Subtype.ext hj⟩⟩
    have hf : Function.Bijective f := by
      refine ⟨?_, ?_⟩
      · intro x y h
        exact Subtype.ext (funext fun i ↦ congrArg (fun e : Fin k ≃ s ↦ (e i).val) h)
      · intro e
        let g (i : Fin k) := (e i).val
        have hg : g ∈ G := mem_injectiveCommonLabels.mpr
          ⟨Subtype.val_injective.comp e.injective, fun i ↦ hsC (e i).property⟩
        have hgs : supp g = s := by
          ext i
          constructor
          · intro hi
            obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hi
            exact (e j).property
          · intro hi
            obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, congrArg Subtype.val hj⟩
        refine ⟨⟨g, Finset.mem_filter.mpr ⟨hg, hgs⟩⟩, ?_⟩
        exact Equiv.ext fun i ↦ Subtype.ext rfl
    let t : Fin k ≃ s := Fintype.equivOfCardEq (by rw [Fintype.card_coe, Fintype.card_fin, hsk])
    have h := Fintype.card_congr (Equiv.ofBijective f hf)
    rw [Fintype.card_coe, ← Fintype.card_congr (Equiv.equivCongr (Equiv.refl (Fin k)) t),
      Fintype.card_perm, Fintype.card_fin] at h
    exact h
  calc
    _ = ∑ x ∈ G, ∏ i ∈ supp x, r i := by
      refine Finset.sum_congr rfl fun x hx ↦ ?_
      exact (Finset.prod_image (mem_injectiveCommonLabels.mp hx).1.injOn).symm
    _ = ∑ s ∈ C.powersetCard k, ∑ x ∈ G.filter (fun x ↦ supp x = s), ∏ i ∈ s, r i :=
      (Finset.sum_fiberwise_of_maps_to' hm (fun s ↦ ∏ i ∈ s, r i)).symm
    _ = _ := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun s hs ↦ ?_
      simp only [Finset.sum_const, nsmul_eq_mul, hcard s hs]

/-- A length-`k` cycle has `(k - 1)!` cyclic orders of its support. -/
private theorem sum_commonForwardCycles_singleton (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) :
    (∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i) =
      ((k - 1).factorial : ℝ) * ∑ s ∈ C.powersetCard k, ∏ i ∈ s, p i := by
  classical
  let S := commonForwardCycles C {k}
  have hm (σ : Equiv.Perm ι) (hσ : σ ∈ S) : σ.support ∈ C.powersetCard k := by
    obtain ⟨-, hsub, hlen⟩ := mem_commonForwardCycles.mp hσ
    exact Finset.mem_powersetCard.mpr ⟨hsub, Finset.mem_singleton.mp hlen⟩
  rw [← Finset.sum_fiberwise_of_maps_to' hm (fun s ↦ ∏ i ∈ s, p i), Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs ↦ ?_
  obtain ⟨hsub, hlen⟩ := Finset.mem_powersetCard.mp hs
  have hfiber : S.filter (fun σ ↦ σ.support = s) =
      Finset.univ.filter (fun σ : Equiv.Perm ι ↦ σ.IsCycle ∧ σ.support = s) := by
    ext σ
    simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_singleton,
      Finset.mem_univ, true_and, S]
    exact ⟨fun h ↦ ⟨h.1.1, h.2⟩, fun h ↦
      ⟨⟨h.1, h.2.symm ▸ hsub, (congrArg Finset.card h.2).trans hlen⟩, h.2⟩⟩
  rw [hfiber, Finset.sum_const, nsmul_eq_mul, card_cyclesWithSupport s (hlen.symm ▸ hk), hlen]

/-- A union bound for repeated labels and for labels outside the common set. -/
noncomputable def commonForwardLabelLoss (C : Finset ι) (p : ι → ℝ) (k : ℕ) : ℝ :=
  (k.choose 2 : ℝ) * (∑ i, (p i) ^ 2) + (k : ℝ) * ∑ i ∈ Cᶜ, p i

/-- A maximum label weight controls collisions and the total omitted weight. -/
theorem commonForwardLabelLoss_le_of_weight_le (C : Finset ι) (p : ι → ℝ) (k : ℕ)
    (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) {q : ℝ} (hq : ∀ i, p i ≤ q) :
    commonForwardLabelLoss C p k ≤ ((k.choose 2 : ℝ) + k * (Cᶜ.card : ℝ)) * q := by
  have hsq : (∑ i, (p i) ^ 2) ≤ q := by
    calc
      _ ≤ ∑ i, p i * q := Finset.sum_le_sum fun i _ ↦ by
        rw [pow_two]
        exact mul_le_mul_of_nonneg_left (hq i) (hp i)
      _ = _ := by rw [← Finset.sum_mul, hp₁, one_mul]
  have hC : (∑ i ∈ Cᶜ, p i) ≤ (Cᶜ.card : ℝ) * q := by
    calc
      _ ≤ ∑ _i ∈ Cᶜ, q := Finset.sum_le_sum fun i _ ↦ hq i
      _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]
  unfold commonForwardLabelLoss
  calc
    _ ≤ (k.choose 2 : ℝ) * q + (k : ℝ) * ((Cᶜ.card : ℝ) * q) :=
      add_le_add (mul_le_mul_of_nonneg_left hsq (Nat.cast_nonneg _))
        (mul_le_mul_of_nonneg_left hC (Nat.cast_nonneg _))
    _ = _ := by ring

/-- The reference weight of common length-`k` cycles is at least the good-label fraction over `k`. -/
theorem commonForwardCycleReferenceWeight_lower (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1) :
    (1 - commonForwardLabelLoss C p k) / (k : ℝ) ≤
      ∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i := by
  classical
  let r (i : ι) := ENNReal.ofReal (p i)
  let E : ℝ := ∑ s ∈ C.powersetCard k, ∏ i ∈ s, p i
  let B := ∑ x ∈ injectiveCommonLabels C k, ∏ i, r (x i)
  have hr : ∑ i, r i = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i), hp₁, ENNReal.ofReal_one]
  have hB : B = ENNReal.ofReal ((k.factorial : ℝ) * E) := by
    rw [show B = _ from sum_injectiveCommonLabels_eq C k r, ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_natCast]
    congr 1
    unfold E
    rw [ENNReal.ofReal_sum_of_nonneg (fun _ _ ↦ Finset.prod_nonneg fun i _ ↦ hp i)]
    exact Finset.sum_congr rfl fun s _ ↦
      (ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ hp i)).symm
  have hlow : ENNReal.ofReal (1 - commonForwardLabelLoss C p k) ≤ B := by
    -- With no forbidden arcs, only the exclusions and collisions matter.
    -- Use a fixed-point-free cyclic successor to apply the label bound.
    let : NeZero k := ⟨by omega⟩
    have hne : (1 : Fin k) ≠ 0 := by
      intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_one', Fin.val_zero, Nat.mod_eq_of_lt (show 1 < k by omega)] at hv
      omega
    let e : Fin k → Fin k := fun i ↦ i + 1
    have he (i : Fin k) : e i ≠ i := by
      change i + 1 ≠ i
      intro hi
      have h := add_left_cancel (b := (1 : Fin k)) (c := 0) (hi.trans (add_zero i).symm)
      exact hne h
    have h := iidLabelGood_sum_weights_lower r hr Cᶜ (fun _ ↦ ∅) e he 0
      (fun _ ↦ by simp)
    simp only [Fintype.card_fin, mul_zero, add_zero] at h
    have hnonneg : 0 ≤ commonForwardLabelLoss C p k := add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ ↦ hp i))
    have hcast : ENNReal.ofReal (commonForwardLabelLoss C p k) =
        (k.choose 2 : ℝ≥0∞) * (∑ i, (r i) ^ 2) + (k : ℝ≥0∞) * ∑ i ∈ Cᶜ, r i := by
      rw [commonForwardLabelLoss, ENNReal.ofReal_add (by positivity)
          (mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ ↦ hp i)),
        ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_natCast, ENNReal.ofReal_natCast,
        ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ sq_nonneg (p i)),
        ENNReal.ofReal_sum_of_nonneg (fun i _ ↦ hp i)]
      simp only [r, ENNReal.ofReal_pow (hp _)]
    rw [ENNReal.ofReal_sub _ hnonneg, ENNReal.ofReal_one, hcast]
    refine h.trans_eq (Finset.sum_congr ?_ fun _ _ ↦ rfl)
    ext x
    simp [iidLabelGood, mem_injectiveCommonLabels]
  have hE0 : 0 ≤ (k.factorial : ℝ) * E :=
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun _ _ ↦
      Finset.prod_nonneg fun i _ ↦ hp i)
  have hlow' := (ENNReal.ofReal_le_ofReal_iff hE0).mp (hB ▸ hlow)
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast (show 0 < k by omega)
  have hf : (k : ℝ) * ((k - 1).factorial : ℝ) = (k.factorial : ℝ) := by
    exact_mod_cast Nat.mul_factorial_pred (show k ≠ 0 by omega)
  rw [sum_commonForwardCycles_singleton C hk p]
  apply (div_le_iff₀ hk0).mpr
  calc
    _ ≤ (k.factorial : ℝ) * E := hlow'
    _ = _ := by rw [← hf]; ring

end ReferenceWeights

section NearRankOne

variable [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)]

/-- Each off-diagonal arc on the common labels has at least this fraction of its reference weight. -/
def CommonForwardArcLower (ν : ι → Measure (Option ι)) (C : Finset ι) (p : ι → ℝ)
    (δ : ℝ) : Prop :=
  ∀ i ∈ C, ∀ j ∈ C, i ≠ j → (1 - δ) * p j ≤ (ν i).real {some j}

/-- Multiplying the row bounds along each cycle gives a lower bound at a fixed length. -/
theorem integral_commonForwardCycles_singleton_lower (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {k : ℕ} (hk : 2 ≤ k)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ≤ 1) (harc : CommonForwardArcLower ν C p δ) :
    (1 - δ) ^ k * ((1 - commonForwardLabelLoss C p k) / (k : ℝ)) ≤
      ∫ f, (realizedForwardCycleCount (commonForwardCycles C {k}) f : ℝ) ∂Measure.pi ν := by
  classical
  have h0 := sub_nonneg.mpr hδ
  rw [integral_realizedForwardCycleCount]
  calc
    _ ≤ (1 - δ) ^ k * ∑ σ ∈ commonForwardCycles C {k}, ∏ i ∈ σ.support, p i :=
      mul_le_mul_of_nonneg_left (commonForwardCycleReferenceWeight_lower C hk p hp hp₁)
        (pow_nonneg h0 k)
    _ = _ := Finset.mul_sum ..
    _ ≤ _ := by
      refine Finset.sum_le_sum fun σ hσ ↦ ?_
      obtain ⟨hcyc, hC, hlen⟩ := mem_commonForwardCycles.mp hσ
      rw [measureReal_forwardCycleEvent ν hcyc, ← Finset.mem_singleton.mp hlen,
        ← Finset.prod_const, ← σ.prod_comp σ.support p (fun _ hi ↦ Equiv.Perm.mem_support.mpr hi),
        ← Finset.prod_mul_distrib]
      exact Finset.prod_le_prod₀ (fun i _ ↦ mul_nonneg h0 (hp _)) fun i hi ↦
        harc i (hC hi) (σ i) (hC (Equiv.Perm.apply_mem_support.mpr hi))
          (Ne.symm (Equiv.Perm.mem_support.mp hi))

/-- The expectation of the length window is the sum of the length-specific expectations. -/
theorem integral_commonForwardCycleCount_eq_sum_lengths (ν : Measure (ι → Option ι))
    [IsFiniteMeasure ν] (C : Finset ι) (L : ℕ) :
    (∫ f, (commonForwardCycleCount C L f : ℝ) ∂ν) =
      ∑ k ∈ Finset.Icc 2 L,
        ∫ f, (realizedForwardCycleCount (commonForwardCycles C {k}) f : ℝ) ∂ν := by
  classical
  unfold commonForwardCycleCount
  simp only [integral_realizedForwardCycleCount]
  let S := commonForwardCycles C (Finset.Icc 2 L)
  have hm (σ : Equiv.Perm ι) (hσ : σ ∈ S) : σ.support.card ∈ Finset.Icc 2 L :=
    (mem_commonForwardCycles.mp hσ).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun σ ↦ ν.real (forwardCycleEvent σ))]
  refine Finset.sum_congr rfl fun k hk ↦ Finset.sum_congr ?_ (fun _ _ ↦ rfl)
  ext σ
  simp only [Finset.mem_filter, mem_commonForwardCycles, Finset.mem_singleton, S]
  constructor
  · rintro ⟨⟨hσ, hC, -⟩, hlen⟩
    exact ⟨hσ, hC, hlen⟩
  · rintro ⟨hσ, hC, rfl⟩
    exact ⟨⟨hσ, hC, hk⟩, rfl⟩

/-- The sum of the inverse lengths over the short-cycle window. -/
noncomputable def commonForwardCycleHarmonic (L : ℕ) : ℝ :=
  ∑ k ∈ Finset.Icc 2 L, (1 : ℝ) / k

omit [MeasurableSpace (Option ι)] [MeasurableSingletonClass (Option ι)] in
/-- The common-label collision and omission bound grows with the number of labels drawn. -/
theorem commonForwardLabelLoss_mono (C : Finset ι) (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) :
    Monotone (commonForwardLabelLoss C p) := by
  intro a b hab
  unfold commonForwardLabelLoss
  exact add_le_add (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.choose_le_choose 2 hab)
    (Finset.sum_nonneg fun _ _ ↦ sq_nonneg _))
    (mul_le_mul_of_nonneg_right (by exact_mod_cast hab) (Finset.sum_nonneg fun i _ ↦ hp i))

omit [Fintype ι] [DecidableEq ι] [MeasurableSpace (Option ι)]
    [MeasurableSingletonClass (Option ι)] in
/-- Removing the length-one term costs at most one in the harmonic lower bound. -/
theorem commonForwardCycleHarmonic_lower {L : ℕ} (hL : 2 ≤ L) :
    Real.log (L : ℝ) - 1 ≤ commonForwardCycleHarmonic L := by
  have h₁ : 1 ∈ Finset.Icc 1 L := Finset.mem_Icc.mpr ⟨le_rfl, by omega⟩
  have he : (Finset.Icc 1 L).erase 1 = Finset.Icc 2 L := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_Icc]
    omega
  have hh := log_add_one_le_harmonic L
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hh
  rw [← Finset.sum_erase_add (Finset.Icc 1 L) (fun j ↦ (j : ℝ)⁻¹) h₁, he,
    Nat.cast_one, inv_one] at hh
  have hlog : Real.log (L : ℝ) ≤ Real.log ((L + 1 : ℕ) : ℝ) :=
    Real.log_le_log (by positivity) (by exact_mod_cast Nat.le_succ L)
  unfold commonForwardCycleHarmonic
  simp only [one_div]
  linarith only [hh, hlog]

/-- Small cumulative arc and label losses preserve a logarithmic mean. -/
theorem integral_commonForwardCycleCount_lower_log (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (19 / 20 : ℝ) * Real.log (L : ℝ) ≤
      ∫ f, (commonForwardCycleCount C L f : ℝ) ∂Measure.pi ν := by
  let c : ℝ := 99 / 100
  have hc : 0 ≤ c := by norm_num [c]
  have hpow : c ≤ (1 - δ) ^ L := by
    have h := one_add_mul_le_pow (a := -δ) (by linarith only [hδ.2]) L
    simp only [← sub_eq_add_neg, mul_neg] at h
    dsimp [c]
    linarith only [h, harcLoss]
  rw [integral_commonForwardCycleCount_eq_sum_lengths]
  calc
    _ ≤ (c * c) * (Real.log (L : ℝ) - 1) := by dsimp [c]; linarith only [hlog]
    _ ≤ (c * c) * commonForwardCycleHarmonic L :=
      mul_le_mul_of_nonneg_left (commonForwardCycleHarmonic_lower hL) (mul_nonneg hc hc)
    _ ≤ _ := by
      rw [commonForwardCycleHarmonic, Finset.mul_sum]
      refine Finset.sum_le_sum fun k hk ↦ ?_
      obtain ⟨hk₂, hkL⟩ := Finset.mem_Icc.mp hk
      refine le_trans ?_ (integral_commonForwardCycles_singleton_lower ν C hk₂ p hp hp₁ hδ.2 harc)
      rw [mul_assoc, mul_one_div]
      have hlabel := (commonForwardLabelLoss_mono C p hp hkL).trans hlabelLoss
      exact mul_le_mul (hpow.trans (pow_le_pow_of_le_one (sub_nonneg.mpr hδ.2)
        (sub_le_self _ hδ.1) hkL)) (div_le_div_of_nonneg_right (by dsimp [c]; linarith only [hlabel])
          (Nat.cast_nonneg k)) (div_nonneg hc (Nat.cast_nonneg k))
          (pow_nonneg (sub_nonneg.mpr hδ.2) _)

/-- The cycle variance is at most its mean. Applying Chebyshev at one nineteenth of the mean
bounds the probability of falling below nine tenths of the logarithm. -/
theorem measure_lt_commonForwardCycleCount_le (ν : ι → Measure (Option ι))
    [∀ i, IsProbabilityMeasure (ν i)] (C : Finset ι) {L : ℕ} (hL : 2 ≤ L)
    (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp₁ : ∑ i, p i = 1)
    {δ : ℝ} (hδ : δ ∈ Icc 0 1) (harc : CommonForwardArcLower ν C p δ)
    (harcLoss : (L : ℝ) * δ ≤ 1 / 100) (hlabelLoss : commonForwardLabelLoss C p L ≤ 1 / 100)
    (hlog : 100 ≤ Real.log (L : ℝ)) :
    (Measure.pi ν) {f | (commonForwardCycleCount C L f : ℝ) < (9 / 10 : ℝ) * Real.log L} ≤
      ENNReal.ofReal (1200 / Real.log (L : ℝ)) := by
  let B := Real.log (L : ℝ)
  let X (f : ι → Option ι) := (commonForwardCycleCount C L f : ℝ)
  let m := ∫ f, X f ∂Measure.pi ν
  have hm : (19 / 20 : ℝ) * B ≤ m :=
    integral_commonForwardCycleCount_lower_log ν C hL p hp hp₁ hδ harc harcLoss hlabelLoss hlog
  have hB : 0 < B := by linarith only [hlog]
  have hm₀ : 0 < m := by linarith only [hB, hm]
  have hsub : {f | X f < 9 / 10 * B} ⊆ {f | m / 19 ≤ |X f - m|} := by
    intro f hf
    change X f < 9 / 10 * B at hf
    change m / 19 ≤ |X f - m|
    rw [abs_sub_comm]
    exact le_trans (by linarith only [hf, hm] : m / 19 ≤ m - X f) (le_abs_self _)
  have hvar : Var[X; Measure.pi ν] ≤ m :=
    variance_realizedForwardCycleCount_le ν _ (fun _ hσ ↦ (mem_commonForwardCycles.mp hσ).1)
  refine (measure_mono hsub).trans ((meas_ge_le_variance_div_sq
    (realizedForwardCycleCount_memLp (Measure.pi ν) _) (by positivity : 0 < m / 19)).trans
    (ENNReal.ofReal_le_ofReal ((div_le_div_of_nonneg_right hvar (sq_nonneg _)).trans ?_)))
  calc
    m / (m / 19) ^ 2 = 361 / m := by field_simp; ring
    _ ≤ 380 / B := (div_le_div_iff₀ hm₀ hB).mpr (by linarith only [hm])
    _ ≤ 1200 / B := div_le_div_of_nonneg_right (by norm_num) hB.le

end NearRankOne

end LennonPittelFormalization
