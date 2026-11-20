module

public import LennonPittel.PivotPairEnvelopeBounds

/-!
# The Lennon–Pittel lower tail

The explicit logarithmic cutoffs work for every fixed choice of abundance
parameters. The positive lower scale is independent of the requested
variance error.
-/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization

/-- The stable-count tail tends to one at every threshold vanishing relative
to the mean. The threshold need not be positive or monotone. -/
theorem lennonPittel_lowerTail (ε : ℕ → ℝ) (hε : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≥ ε n * expectedNumStableMatchings n}) atTop (𝓝 1) := by
  apply lennonPittel_of_remaining_pivot_pair_estimates _ ε hε
  intro b A B κ hb _ _ _ hκ hκb _ _
  exact ⟨logarithmicCycleCutoff, tendsto_logarithmicCycleCutoff,
    logarithmic_pivotPairIntegrals_isLittleO (A := A) (B := B) hb hκ hκb⟩

/-- The exact statement in the Formal Conjectures repository. -/
theorem lennon_pittel_conjecture_verified
    (ε : ℕ → ℝ) (_hε_pos : ∀ n, 0 < ε n) (_hε_antitone : Antitone ε)
    (hε_tendsto : Tendsto ε atTop (𝓝 0)) :
    Tendsto (fun n ↦ (StableMarriage.uniformProfile n).toMeasure
      {p | (StableMarriage.numStableMatchings p : ℝ) ≥
        ε n * StableMarriage.expectedNumStableMatchings n}) atTop (𝓝 1) :=
  lennonPittel_lowerTail ε hε_tendsto

end LennonPittelFormalization
