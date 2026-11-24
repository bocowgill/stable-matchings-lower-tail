/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
module

public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Order.LiminfLimsup
public import Mathlib.Data.Fintype.Perm
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Probability.ProbabilityMassFunction.Integrals

@[expose] public section

/-!
# A quantitative lower tail for random stable matchings

In a balanced market of size `n` on each side, each participant chooses an
independent uniform strict ranking of the other side. The probability below
uses the uniform law on the product of all these ranking spaces. The count
ranges over complete matchings with no blocking pair.

The fixed-threshold proposition in *How Many Stable Matchings in a Random
Market?* fixes `t` before taking the limit superior over `n`.
-/

open scoped ENNReal

namespace PMF

/-- The uniform probability mass function on a nonempty finite type. -/
noncomputable def fintypeUniform (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  ofFintype (fun _ ↦ (Fintype.card α : ℝ≥0∞)⁻¹) (by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ENNReal.mul_inv_cancel]
    · exact_mod_cast Fintype.card_ne_zero
    · exact ENNReal.natCast_ne_top _)

@[simp]
theorem fintypeUniform_apply {α : Type*} [Fintype α] [Nonempty α] (a : α) :
    fintypeUniform α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [fintypeUniform]

end PMF

namespace StableMarriage

/-- A preference profile for `n` men and `n` women. Each permutation maps a candidate to their
rank, with lower ranks preferred. -/
structure Profile (n : ℕ) where
  /-- The rank that each man assigns to each woman. -/
  manRank : Fin n → Equiv.Perm (Fin n)
  /-- The rank that each woman assigns to each man. -/
  womanRank : Fin n → Equiv.Perm (Fin n)
  deriving Inhabited

/-- Preference profiles form a finite type. -/
instance {n : ℕ} : Fintype (Profile n) :=
  Fintype.ofEquiv
    ((Fin n → Equiv.Perm (Fin n)) × (Fin n → Equiv.Perm (Fin n)))
    { toFun := fun p => ⟨p.1, p.2⟩
      invFun := fun p => (p.manRank, p.womanRank)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- A complete matching of `n` men to `n` women. -/
abbrev Matching (n : ℕ) := Equiv.Perm (Fin n)

/-- A man and woman form a blocking pair when they are not matched to each other and each ranks
the other above their current partner. -/
def IsBlockingPair {n : ℕ} (p : Profile n) (μ : Matching n) (m w : Fin n) : Prop :=
  μ m ≠ w ∧
    p.manRank m w < p.manRank m (μ m) ∧
      p.womanRank w m < p.womanRank w (μ.symm w)

/-- A matching is stable when it has no blocking pair. -/
def IsStable {n : ℕ} (p : Profile n) (μ : Matching n) : Prop :=
  ∀ m w, ¬ IsBlockingPair p μ m w

/-- The number of stable complete matchings for a preference profile. -/
noncomputable def numStableMatchings {n : ℕ} (p : Profile n) : ℕ := by
  classical
  exact Fintype.card {μ : Matching n // IsStable p μ}

/-- The discrete measurable structure on preference profiles. -/
instance {n : ℕ} : MeasurableSpace (Profile n) := ⊤

/-- The uniform probability mass function on preference profiles. -/
noncomputable def uniformProfile (n : ℕ) : PMF (Profile n) :=
  PMF.fintypeUniform (Profile n)

end StableMarriage

open Filter

namespace LennonPittel

/-- For every sufficiently small fixed positive threshold `t`, the limiting
upper probability that the number of stable matchings is at most `t * n * log n`
is bounded by an absolute constant times `t^2 * log (exp 1 / t)`. -/
theorem fixed_threshold_lower_tail :
    ∃ C t₀ : ℝ, 0 < C ∧ 0 < t₀ ∧ ∀ t : ℝ, 0 < t → t < t₀ →
      limsup (fun n : ℕ ↦ ((StableMarriage.uniformProfile n).toMeasure
        {p | (StableMarriage.numStableMatchings p : ℝ) ≤
          t * ((n : ℝ) * Real.log n)}).toReal) atTop ≤ C * t ^ 2 * Real.log (Real.exp 1 / t) := by
  sorry

end LennonPittel
