module

public import LennonPittel.CoexposedRotations
public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The number of exposed rotations
-/

@[expose] public section

open StableMarriage
open scoped BigOperators

namespace LennonPittelFormalization

variable {n : ℕ} {p : Profile n} {μ : Matching n}

/-- The number of exposed rotations at a matching. -/
noncomputable def numExposedRotations (p : Profile n) (μ : Matching n) : ℕ :=
  Nat.card {ρ : Equiv.Perm (Fin n) // IsExposedRotation p μ ρ}

end LennonPittelFormalization
