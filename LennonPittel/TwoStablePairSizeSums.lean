module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Factorial.BigOperators
public import Mathlib.NumberTheory.Harmonic.Bounds

/-!
# Summing the two-stable-matching size bound

The size kernel is the factorial-ratio envelope in the two-matching estimate,
without the common factor proportional to one plus the logarithm of the market size.
In each row its normalized weights give the distribution of the minimum of a uniform
subset. The row mass and first moment control all three size sums.
-/

@[expose] public section

open Finset

namespace LennonPittelFormalization

/-- Both orientations are nontrivial and use disjoint sets of labels. -/
def ValidPairSizes (n : ℕ) (p : ℕ × ℕ) : Prop :=
  2 ≤ p.1 ∧ 2 ≤ p.2 ∧ p.1 + p.2 ≤ n

/-- The size-dependent factor in the upper bound for incomparable pairs. -/
noncomputable def twoStablePairSizeKernel (n : ℕ) (p : ℕ × ℕ) : ℝ :=
  (n : ℝ) ^ 3 / ((↑(n - p.1) : ℝ) * ↑(n - p.2)) *
    ((↑((n - p.1).descFactorial p.2) : ℝ) / ↑(n.descFactorial p.2))

theorem twoStablePairSizeKernel_nonneg (n : ℕ) (p : ℕ × ℕ) :
    0 ≤ twoStablePairSizeKernel n p := by
  unfold twoStablePairSizeKernel
  positivity

private theorem cast_descFactorial_eq_div {n k : ℕ} (hk : k ≤ n) :
    (n.descFactorial k : ℝ) = (↑n.factorial : ℝ) / ↑(n - k).factorial := by
  apply (eq_div_iff (by positivity)).2
  rw [mul_comm]
  exact_mod_cast Nat.factorial_mul_descFactorial hk

/-- The kernel does not distinguish the two orientations. -/
theorem twoStablePairSizeKernel_swap {n u v : ℕ} (h : u + v ≤ n) :
    twoStablePairSizeKernel n (v, u) = twoStablePairSizeKernel n (u, v) := by
  have hu : u ≤ n := by omega
  have hv : v ≤ n := by omega
  have huv : u ≤ n - v := by omega
  have hvu : v ≤ n - u := by omega
  have ht : n - v - u = n - u - v := by omega
  change (n : ℝ) ^ 3 / (↑(n - v) * ↑(n - u)) *
      (↑((n - v).descFactorial u) / ↑(n.descFactorial u)) =
    (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
      (↑((n - u).descFactorial v) / ↑(n.descFactorial v))
  rw [cast_descFactorial_eq_div hu, cast_descFactorial_eq_div hv,
    cast_descFactorial_eq_div huv, cast_descFactorial_eq_div hvu, ht]
  rw [mul_comm (↑(n - v) : ℝ) ↑(n - u)]
  congr 1
  field_simp

/-- Factorial value of the beta integral with parameters k and n - k. -/
noncomputable def pairSizeBetaFactor (n k : ℕ) : ℝ :=
  (↑(k - 1).factorial : ℝ) * ↑(n - k - 1).factorial / ↑(n - 1).factorial

private theorem cast_factorial_pred {k : ℕ} (hk : 0 < k) :
    (k.factorial : ℝ) = (k : ℝ) * ↑(k - 1).factorial := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp [Nat.factorial_succ]

/-- The beta factors and the unrestricted labeled-pair multiplier simplify to the
falling-factorial kernel. The two orientation derangement fractions are separate. -/
theorem twoStablePairSizeKernel_eq_beta_factors {n u v : ℕ} (h : ValidPairSizes n (u, v)) :
    twoStablePairSizeKernel n (u, v) =
      ((n.factorial : ℝ) ^ 2 / ↑(n - u - v).factorial) *
        (pairSizeBetaFactor n u * pairSizeBetaFactor n v /
          ((↑(n - 1).factorial : ℝ) * ↑(u - 1).factorial * ↑(v - 1).factorial)) := by
  obtain ⟨hu, hv, huv⟩ := h
  have hvn : v ≤ n := by omega
  have hvu : v ≤ n - u := by omega
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  have hn : 0 < n := by omega
  calc
    _ = (n : ℝ) ^ 3 * ↑(n - u - 1).factorial * ↑(n - v - 1).factorial /
        (↑(n - u - v).factorial * ↑n.factorial) := by
      change (n : ℝ) ^ 3 / (↑(n - u) * ↑(n - v)) *
        (↑((n - u).descFactorial v) / ↑(n.descFactorial v)) = _
      rw [cast_descFactorial_eq_div hvu, cast_descFactorial_eq_div hvn,
        cast_factorial_pred hnu, cast_factorial_pred hnv]
      field_simp
    _ = _ := by
      unfold pairSizeBetaFactor
      rw [cast_factorial_pred hn]
      field_simp

private theorem cast_choose_eq_factorial_div {a b : ℕ} (h : b ≤ a) :
    (a.choose b : ℝ) = (a.factorial : ℝ) / (b.factorial * ((a - b).factorial : ℝ)) := by
  apply (eq_div_iff (by positivity)).2
  rw [← mul_assoc]
  exact_mod_cast Nat.choose_mul_factorial_mul_factorial h

/-- In row `u`, the kernel is the mass function of the minimum of a uniform
`u`-subset of the first `n - 1` labels, scaled by `n²/u`. -/
theorem twoStablePairSizeKernel_eq_choose {n u v : ℕ} (hu : 1 ≤ u) (hv : 1 ≤ v)
    (hs : u + v ≤ n) :
    twoStablePairSizeKernel n (u, v) =
      (n : ℝ) ^ 2 / (u : ℝ) / ((n - 1).choose u : ℝ) *
        ((n - v - 1).choose (u - 1) : ℝ) := by
  change (n : ℝ) ^ 3 / ((n - u : ℕ) * ((n - v : ℕ) : ℝ)) *
    (((n - u).descFactorial v : ℝ) / (n.descFactorial v : ℝ)) = _
  rw [cast_descFactorial_eq_div (show v ≤ n - u by omega),
    cast_descFactorial_eq_div (show v ≤ n by omega),
    cast_choose_eq_factorial_div (show u ≤ n - 1 by omega),
    cast_choose_eq_factorial_div (show u - 1 ≤ n - v - 1 by omega),
    show n - 1 - u = n - u - 1 by omega,
    show n - v - 1 - (u - 1) = n - u - v by omega,
    cast_factorial_pred (show 0 < n - u by omega),
    cast_factorial_pred (show 0 < n - v by omega),
    cast_factorial_pred (show 0 < n by omega),
    cast_factorial_pred hu]
  have hnu : 0 < n - u := by omega
  have hnv : 0 < n - v := by omega
  field_simp

private theorem sum_row_choose_from {n u a : ℕ} (hu : 1 ≤ u) (ha : a ≤ n - u)
    (hun : u ≤ n) :
    (∑ v ∈ Icc a (n - u), (n - v - 1).choose (u - 1)) = (n - a).choose u := by
  calc
    _ = ∑ j ∈ Icc (u - 1) (n - a - 1), j.choose (u - 1) := by
      refine sum_nbij' (fun v ↦ n - v - 1) (fun j ↦ n - j - 1) ?_ ?_ ?_ ?_ (fun _ _ ↦ rfl)
        <;> intro i hi <;> simp only [mem_Icc] at * <;> omega
    _ = _ := by rw [Nat.sum_Icc_choose]; congr 1 <;> omega

private theorem sum_row_choose {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), (n - v - 1).choose (u - 1)) = (n - 1).choose u :=
  sum_row_choose_from hu (by omega) hun.le

private theorem sum_mul_row_choose {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), v * (n - v - 1).choose (u - 1)) = n.choose (u + 1) := by
  have h := sum_Ico_Ico_comm 1 (n - u + 1) (fun _ v ↦ (n - v - 1).choose (u - 1))
  simp only [Ico_add_one_right_eq_Icc, sum_const, Nat.card_Icc, nsmul_eq_mul,
    Nat.add_sub_cancel, Nat.cast_id] at h
  rw [← h]
  calc
    _ = ∑ i ∈ Icc 1 (n - u), (n - i).choose u := by
      exact sum_congr rfl fun i hi ↦ sum_row_choose_from hu (mem_Icc.mp hi).2 hun.le
    _ = n.choose (u + 1) := by
      have h' := sum_row_choose (n := n + 1) (u := u + 1) (by omega) (by omega)
      simpa only [Nat.add_sub_add_right, Nat.add_sub_cancel, Nat.sub_sub] using h'

/-- The full row of the size kernel sums to the harmonic weight. -/
theorem sum_twoStablePairSizeKernel_row {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n - u), twoStablePairSizeKernel n (u, v)) = (n : ℝ)^2 / u := by
  have hpos : 0 < ((n - 1).choose u : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : u ≤ n - 1)
  calc
    _ = ((n : ℝ)^2 / u / ((n - 1).choose u : ℝ)) *
        ∑ v ∈ Icc 1 (n-u), ((n-v-1).choose (u-1) : ℝ) := by
      rw [mul_sum]
      exact sum_congr rfl fun v hv ↦ twoStablePairSizeKernel_eq_choose hu (mem_Icc.mp hv).1
        (by have := (mem_Icc.mp hv).2; omega)
    _ = _ := by rw [← Nat.cast_sum, sum_row_choose hu hun, div_mul_cancel₀ _ hpos.ne']

/-- The first moment of the row is the harmonic weight times the expected
minimum of a uniform subset of size `u` of `n - 1` labels. -/
theorem sum_mul_twoStablePairSizeKernel_row {n u : ℕ} (hu : 1 ≤ u) (hun : u < n) :
    (∑ v ∈ Icc 1 (n-u), (v : ℝ) * twoStablePairSizeKernel n (u,v)) =
      (n : ℝ)^3 / ((u : ℝ) * (u+1)) := by
  have hpos : 0 < ((n - 1).choose u : ℝ) := by
    exact_mod_cast Nat.choose_pos (by omega : u ≤ n - 1)
  have hchoose : (n:ℝ) * ((n-1).choose u : ℝ) = (n.choose (u+1) : ℝ) * (u+1) := by
    exact_mod_cast (show n * (n-1).choose u = n.choose (u+1) * (u+1) by
      simpa only [Nat.sub_add_cancel (by omega : 1 ≤ n)] using Nat.add_one_mul_choose_eq (n-1) u)
  calc
    _ = ((n : ℝ)^2 / u / ((n-1).choose u : ℝ)) *
        ∑ v ∈ Icc 1 (n-u), ((v * (n-v-1).choose (u-1) : ℕ) : ℝ) := by
      rw [mul_sum]
      refine sum_congr rfl fun v hv ↦ ?_
      rw [twoStablePairSizeKernel_eq_choose hu (mem_Icc.mp hv).1
        (by have := (mem_Icc.mp hv).2; omega : u+v ≤ n), Nat.cast_mul]
      ring
    _ = _ := by
      rw [← Nat.cast_sum, sum_mul_row_choose hu hun]
      have hu' : (0:ℝ) < u := by exact_mod_cast hu
      field_simp
      linear_combination (n:ℝ)^2 * hchoose.symm

private theorem sum_by_row_le {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (t : Finset ℕ) (ht : ∀ p ∈ s, p.1 ∈ t)
    (g : ℕ → ℝ) (hg : ∀ u ∈ t, 0 ≤ g u)
    (hrow : ∀ u ∈ t, 2 ≤ u → u + 2 ≤ n →
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤ g u) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ ∑ u ∈ t, g u := by
  rw [← sum_fiberwise_of_maps_to ht]
  refine sum_le_sum fun u hu ↦ ?_
  by_cases he : s.filter (fun p ↦ p.1 = u) = ∅
  · simpa [he] using hg u hu
  obtain ⟨p, hp⟩ := nonempty_iff_ne_empty.mpr he
  obtain ⟨hps, hpu⟩ := mem_filter.mp hp
  obtain ⟨h₁,h₂,h₃⟩ := hs p hps
  subst u
  exact hrow _ hu h₁ (by omega)

private theorem sum_fiber_le_of_row {n u : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (f : ℕ → ℝ) (hf : ∀ v, 0 ≤ f v)
    (h : ∀ p ∈ s, p.1 = u → twoStablePairSizeKernel n p ≤ f p.2) :
    (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤
      ∑ v ∈ Icc 1 (n-u), f v := by
  let row := s.filter (fun p ↦ p.1 = u)
  have hbox : row ⊆ {u} ×ˢ Icc 1 (n-u) := by
    intro p hp
    obtain ⟨hps, hu⟩ := mem_filter.mp hp
    obtain ⟨_, hv, hn⟩ := hs p hps
    exact mem_product.mpr ⟨mem_singleton.mpr hu, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  calc
    _ ≤ ∑ p ∈ row, f p.2 := sum_le_sum fun p hp ↦ h p (mem_filter.mp hp).1 (mem_filter.mp hp).2
    _ ≤ ∑ p ∈ {u} ×ˢ Icc 1 (n-u), f p.2 := sum_le_sum_of_subset_of_nonneg hbox (fun p _ _ ↦ hf p.2)
    _ = _ := by rw [sum_product, sum_singleton]

private theorem sum_inv_Icc_le_log (m : ℕ) :
    (∑ v ∈ Icc 1 m, (v : ℝ)⁻¹) ≤ 1 + Real.log m := by
  simpa only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    using harmonic_le_one_add_log m

/-- A set of pairs costs at most the harmonic mass of its first coordinates. -/
theorem sum_twoStablePairSizeKernel_le_rows {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) (U : Finset ℕ) (hU : ∀ p ∈ s, p.1 ∈ U) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ)^2 * ∑ u ∈ U, (u : ℝ)⁻¹ := by
  calc
    _ ≤ ∑ u ∈ U, (n : ℝ)^2 / u := by
      apply sum_by_row_le s hs U hU _ (fun _ _ ↦ by positivity)
      intro u _ hu hun
      rw [← sum_twoStablePairSizeKernel_row (by omega : 1 ≤ u) (by omega : u < n)]
      exact sum_fiber_le_of_row s hs _ (fun v ↦ twoStablePairSizeKernel_nonneg n (u,v))
        (by rintro ⟨_,v⟩ _ rfl; exact le_rfl)
    _ = _ := by simp [div_eq_mul_inv, mul_sum]

/-- The full size sum costs a single harmonic sum. -/
theorem sum_twoStablePairSizeKernel_le_total {n : ℕ} (_hn : 0 < n) (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ)^2 * (1 + Real.log n) := by
  calc
    _ ≤ (n : ℝ)^2 * ∑ u ∈ Icc 1 n, (u : ℝ)⁻¹ :=
      sum_twoStablePairSizeKernel_le_rows s hs _ fun p hp ↦
        mem_Icc.mpr ⟨by have := (hs p hp).1; omega, (Nat.le_add_right _ _).trans (hs p hp).2.2⟩
    _ ≤ (n : ℝ)^2 * (1 + Real.log n) :=
      mul_le_mul_of_nonneg_left (sum_inv_Icc_le_log n) (sq_nonneg _)

private theorem sum_row_reciprocals {k n : ℕ} (hk : 0 < k) :
    (∑ u ∈ Icc k n, 1 / ((u : ℝ) * (u + 1))) ≤ 1 / (k : ℝ) := by
  by_cases hkn : k ≤ n
  · let f (j : ℕ) : ℝ := -(1 / (j : ℝ))
    calc
      _ = ∑ u ∈ Icc k n, (f (u + 1) - f u) := by
        refine sum_congr rfl fun u hu ↦ ?_
        have hu' : 0 < (u : ℝ) := Nat.cast_pos.mpr (lt_of_lt_of_le hk (mem_Icc.mp hu).1)
        dsimp [f]
        push_cast
        field_simp
        ring
      _ = f (n + 1) - f k := sum_Icc_sub hkn f
      _ ≤ _ := by dsimp [f]; linarith [show 0 ≤ 1 / ((n + 1 : ℕ) : ℝ) by positivity]
  · rw [Icc_eq_empty_of_lt (lt_of_not_ge hkn), sum_empty]
    positivity

/-- Pairs with both sizes at least a square-root cutoff have quadratic mass. -/
theorem sum_twoStablePairSizeKernel_le_both_long {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p) {b : ℝ} (hb : 0 < b)
    (hl : ∀ p ∈ s, b * Real.sqrt n ≤ (p.1 : ℝ) ∧ b * Real.sqrt n ≤ (p.2 : ℝ)) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ (n : ℝ) ^ 2 / b ^ 2 := by
  let k := ⌈b * Real.sqrt n⌉₊
  have hn' : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hcut : 0 < b * Real.sqrt n := mul_pos hb (Real.sqrt_pos.mpr hn')
  have hle : b * Real.sqrt n ≤ (k : ℝ) := Nat.le_ceil _
  have hk : (0 : ℝ) < k := hcut.trans_le hle
  have hrow (u : ℕ) (hu : 2 ≤ u) (hun : u+2 ≤ n) :
      (∑ p ∈ s.filter (fun p ↦ p.1 = u), twoStablePairSizeKernel n p) ≤
        (n : ℝ)^3 / k * (1 / ((u : ℝ) * (u + 1))) := by
    calc
      _ ≤ ∑ v ∈ Icc 1 (n-u), ((v : ℝ) * twoStablePairSizeKernel n (u,v)) / k := by
        apply sum_fiber_le_of_row s hs _ (fun v ↦ div_nonneg
          (mul_nonneg (Nat.cast_nonneg _) (twoStablePairSizeKernel_nonneg _ _)) hk.le)
        rintro ⟨u',v⟩ hp rfl
        apply (le_div_iff₀ hk).2
        have hv : k ≤ v := Nat.ceil_le.mpr (hl _ hp).2
        simpa only [mul_comm] using mul_le_mul_of_nonneg_right
          (Nat.cast_le.mpr hv : (k : ℝ) ≤ v) (twoStablePairSizeKernel_nonneg n (u',v))
      _ = _ := by rw [← sum_div, sum_mul_twoStablePairSizeKernel_row (by omega : 1 ≤ u) (by omega : u < n)]; ring
  calc
    _ ≤ ∑ u ∈ Icc k n, (n : ℝ)^3 / k * (1 / ((u : ℝ) * (u + 1))) := by
      apply sum_by_row_le s hs (Icc k n) _ _ (fun _ _ ↦ by positivity)
        (fun u _ ↦ hrow u)
      intro p hp
      exact mem_Icc.mpr ⟨Nat.ceil_le.mpr (hl p hp).1,
        (Nat.le_add_right _ _).trans (hs p hp).2.2⟩
    _ ≤ (n : ℝ)^3 / k * (1 / (k : ℝ)) := by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left (sum_row_reciprocals (Nat.cast_pos.mp hk)) (by positivity)
    _ = (n : ℝ)^3 / (k : ℝ)^2 := by ring
    _ ≤ (n : ℝ)^3 / (b * Real.sqrt n)^2 :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) (pow_le_pow_left₀ hcut.le hle _)
    _ = _ := by rw [mul_pow, Real.sq_sqrt hn'.le]; field_simp

private theorem sum_le_filtered_cover {α : Type*} (s : Finset α) (f : α → ℝ)
    (P Q : α → Prop) [DecidablePred P] [DecidablePred Q]
    (hf : ∀ p ∈ s, 0 ≤ f p) (hcov : ∀ p ∈ s, P p ∨ Q p) :
    (∑ p ∈ s, f p) ≤ (∑ p ∈ s.filter P, f p) + ∑ p ∈ s.filter Q, f p := by
  simp only [sum_filter, ← sum_add_distrib]
  refine sum_le_sum fun p hp ↦ ?_
  by_cases hP : P p
  · by_cases hQ : Q p
    · simp only [hP, hQ, ite_true]
      exact le_add_of_nonneg_right (hf p hp)
    · simp [hP, hQ]
  · have hQ := (hcov p hp).resolve_left hP
    simp [hP, hQ]

private def swapSizePairs (s : Finset (ℕ × ℕ)) : Finset (ℕ × ℕ) :=
  s.map (Equiv.prodComm ℕ ℕ).toEmbedding

private theorem mem_swapSizePairs {p : ℕ × ℕ} {s : Finset (ℕ × ℕ)} :
    p ∈ swapSizePairs s ↔ p.swap ∈ s := by
  constructor
  · intro hp
    obtain ⟨q, hq, hqp⟩ := mem_map.mp hp
    change q.swap = p at hqp
    rw [← hqp, Prod.swap_swap]
    exact hq
  · intro hp
    exact mem_map.mpr ⟨p.swap, hp, Prod.swap_swap _⟩

private theorem sum_twoStablePairSizeKernel_swapSizePairs {n : ℕ} (s : Finset (ℕ × ℕ))
    (hs : ∀ p ∈ s, ValidPairSizes n p) :
    (∑ p ∈ swapSizePairs s, twoStablePairSizeKernel n p) =
      ∑ p ∈ s, twoStablePairSizeKernel n p := by
  rw [swapSizePairs, sum_map]
  exact sum_congr rfl fun p hp ↦ twoStablePairSizeKernel_swap (hs p hp).2.2

private theorem validPairSizes_swap {n : ℕ} {p : ℕ × ℕ} (h : ValidPairSizes n p) :
    ValidPairSizes n p.swap := by
  exact ⟨h.2.1, h.1, by simpa [add_comm] using h.2.2⟩

private theorem sum_inv_outside_orientation_interval_le {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hLt : (L : ℝ) ≤ Real.log (n : ℝ)) :
    (∑ u ∈ (Icc 1 n).filter (fun u : ℕ ↦ u < L ∨ n / (Real.log (n : ℝ)) ^ 3 < (u : ℝ)),
      (u : ℝ)⁻¹) ≤ 2 + 4 * Real.log (Real.log (n : ℝ)) := by
  classical
  let t := Real.log (n : ℝ)
  let y := (n : ℝ) / t ^ 3
  let S := (Icc 1 n).filter (fun u : ℕ ↦ u < L ∨ y < (u : ℝ))
  change (∑ u ∈ S, (u : ℝ)⁻¹) ≤ 2 + 4 * Real.log t
  have ht0 : 0 < t := zero_lt_one.trans_le ht
  have hn : (n : ℝ) ≠ 0 := by
    intro h
    norm_num [h] at ht
  have hy0 : 0 ≤ y := div_nonneg (Nat.cast_nonneg _) (pow_nonneg ht0.le _)
  have hyn : y ≤ n := div_le_self (Nat.cast_nonneg _) (one_le_pow₀ ht)
  have hfloor : ⌊y⌋₊ ≤ n := by exact_mod_cast (Nat.floor_le hy0).trans hyn
  have hsub : Icc 1 ⌊y⌋₊ ⊆ Icc 1 n := Icc_subset_Icc_right hfloor
  have lown : S.filter (· < L) ⊆ Icc 1 ⌊t⌋₊ := by
    intro u hu
    obtain ⟨huS, huL⟩ := mem_filter.mp hu
    exact mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp huS).1).1,
      Nat.le_floor ((Nat.cast_le.mpr (Nat.le_of_lt huL)).trans hLt)⟩
  have highn : S.filter (fun u ↦ ¬u < L) ⊆ Icc 1 n \ Icc 1 ⌊y⌋₊ := by
    intro u hu
    obtain ⟨huS, huL⟩ := mem_filter.mp hu
    obtain ⟨hun, huy⟩ := mem_filter.mp huS
    exact mem_sdiff.mpr ⟨hun, fun h ↦ ((Nat.floor_lt hy0).mpr (huy.resolve_left huL)).not_ge
      (mem_Icc.mp h).2⟩
  have hlo := harmonic_floor_le_one_add_log t ht
  have hhi := harmonic_le_one_add_log n
  have hfloorlo := log_le_harmonic_floor y hy0
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast] at hlo hhi hfloorlo
  rw [show Real.log y = t - 3 * Real.log t by
    dsimp only [y]; rw [Real.log_div hn (pow_ne_zero _ ht0.ne'), Real.log_pow]; norm_num [t]] at hfloorlo
  rw [← sum_filter_add_sum_filter_not S (· < L)]
  calc
    _ ≤ (∑ u ∈ Icc 1 ⌊t⌋₊, (u : ℝ)⁻¹) + ∑ u ∈ Icc 1 n \ Icc 1 ⌊y⌋₊, (u : ℝ)⁻¹ :=
      add_le_add (sum_le_sum_of_subset_of_nonneg lown fun _ _ _ ↦ by positivity)
        (sum_le_sum_of_subset_of_nonneg highn fun _ _ _ ↦ by positivity)
    _ ≤ _ := by
      rw [sum_sdiff_eq_sub hsub]
      change _ ≤ 1 + t at hhi
      linarith only [hlo, hhi, hfloorlo]

/-- Both orientation sizes are large enough for the forced cycle test and
small enough that almost every label is common to the two matchings. -/
def RegularOrientationPair (n L : ℕ) (p : ℕ × ℕ) : Prop :=
  L ≤ p.1 ∧ L ≤ p.2 ∧ (p.1 : ℝ) ≤ n / (Real.log n)^3 ∧ (p.2 : ℝ) ≤ n / (Real.log n)^3

/-- Pairs outside the regular rectangle have at least one size in a harmonic tail. -/
theorem sum_twoStablePairSizeKernel_le_not_regularOrientationPair {n L : ℕ}
    (ht : 1 ≤ Real.log (n : ℝ)) (hLt : (L : ℝ) ≤ Real.log (n : ℝ))
    (s : Finset (ℕ × ℕ)) (hs : ∀ p ∈ s, ValidPairSizes n p)
    (he : ∀ p ∈ s, ¬RegularOrientationPair n L p) :
    (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ 2 * (n : ℝ)^2 * (2 + 4 * Real.log (Real.log n)) := by
  classical
  let U := (Icc 1 n).filter fun u : ℕ ↦ u < L ∨ n / (Real.log (n : ℝ))^3 < (u : ℝ)
  have hcover (p) (hp : p ∈ s) : p.1 ∈ U ∨ p.2 ∈ U := by
    obtain ⟨hu, hv, huv⟩ := hs p hp
    have hor : (p.1 < L ∨ n / (Real.log (n : ℝ))^3 < (p.1 : ℝ)) ∨
        (p.2 < L ∨ n / (Real.log (n : ℝ))^3 < (p.2 : ℝ)) := by
      by_contra! h
      exact he p hp ⟨h.1.1, h.2.1, h.1.2, h.2.2⟩
    exact hor.imp
      (fun h ↦ mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)
      (fun h ↦ mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, h⟩)
  let A := s.filter fun p ↦ p.1 ∈ U
  let B := s.filter fun p ↦ p.2 ∈ U
  have hB (p) (hp : p ∈ B) : ValidPairSizes n p := hs p (mem_filter.mp hp).1
  have hA := sum_twoStablePairSizeKernel_le_rows A (fun p hp ↦ hs p (mem_filter.mp hp).1) U
    (fun p hp ↦ (mem_filter.mp hp).2)
  have hB' := sum_twoStablePairSizeKernel_le_rows (swapSizePairs B)
    (fun p hp ↦ by simpa using validPairSizes_swap (hB p.swap (mem_swapSizePairs.mp hp))) U
    (fun _ hp ↦ (mem_filter.mp (mem_swapSizePairs.mp hp)).2)
  rw [sum_twoStablePairSizeKernel_swapSizePairs B hB] at hB'
  calc
    _ ≤ (∑ p ∈ A, twoStablePairSizeKernel n p) + ∑ p ∈ B, twoStablePairSizeKernel n p :=
      sum_le_filtered_cover s _ _ _ (fun p _ ↦ twoStablePairSizeKernel_nonneg n p) hcover
    _ ≤ 2 * (n : ℝ)^2 * ∑ u ∈ U, (u : ℝ)⁻¹ := by linarith only [hA,hB']
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_inv_outside_orientation_interval_le ht hLt)
      (by positivity)

/-- Transfer any of the kernel-sum bounds to a per-size probability or count bound
with the common prefactor from the two-matching estimate. -/
theorem sum_twoStablePairSizeWeights_le {n : ℕ} (hn : 0 < n)
    (s : Finset (ℕ × ℕ)) (w : ℕ × ℕ → ℝ) {C B : ℝ} (hC : 0 ≤ C)
    (hw : ∀ p ∈ s, w p ≤ C * (1 + Real.log n) * twoStablePairSizeKernel n p)
    (hB : (∑ p ∈ s, twoStablePairSizeKernel n p) ≤ B) :
    (∑ p ∈ s, w p) ≤ C * (1 + Real.log n) * B := by
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (Nat.one_le_cast.mpr hn)
  calc
    _ ≤ ∑ p ∈ s, (C * (1 + Real.log n)) * twoStablePairSizeKernel n p := sum_le_sum hw
    _ = (C * (1 + Real.log n)) * ∑ p ∈ s, twoStablePairSizeKernel n p := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hB (by positivity)

end LennonPittelFormalization
