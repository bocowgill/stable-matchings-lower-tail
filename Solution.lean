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

public import LennonPittel.Quantitative.FixedThreshold

/-! # The fixed-threshold lower tail for random stable matchings -/

public section

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
  simpa only [LennonPittelFormalization.fixedThresholdLimsup] using
    LennonPittelFormalization.fixedThreshold_lowerTail

end LennonPittel
