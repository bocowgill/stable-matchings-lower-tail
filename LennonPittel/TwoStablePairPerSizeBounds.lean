module

public import LennonPittel.PivotBackgroundPairBound
public import LennonPittel.TwoStablePairMassSums

/-!
# Per-size bounds on the ordered stable-pair mass

The labeled-pair estimate is uniform over the cycle type. Summing it over
one size bin gives the common kernel. Forced-cycle exceptions restrict the
number of labels; background-cycle exceptions instead reduce their probabilities.
-/

@[expose] public section

open Filter MeasureTheory Set StableMarriage
open scoped ENNReal

namespace LennonPittelFormalization

variable {n : ℕ}

private theorem factorialEnvelope_mul_labeledMass {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) :
    ((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v) =
      ENNReal.ofReal (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  have he : (n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial =
      ENNReal.ofReal ((n.factorial : ℝ) ^ 2 / (n - u - v).factorial) := by
    rw [ENNReal.ofReal_div_of_pos (by positivity), ENNReal.ofReal_pow (by positivity),
      ENNReal.ofReal_natCast, ENNReal.ofReal_natCast]
  rw [he, ← ENNReal.ofReal_mul (by positivity), labeledStablePairMassBound_mul_factorials hs]

private theorem scorePairSizeMass_toReal_le_of_envelope
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {a : ℝ} (ha : 0 ≤ a)
    (h : scorePairSizeMass R (u, v) ≤ ENNReal.ofReal a *
      (((n.factorial : ℝ≥0∞) ^ 2 / (n - u - v).factorial) *
        ENNReal.ofReal (labeledStablePairMassBound n u v))) :
    (scorePairSizeMass R (u, v)).toReal ≤
      a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
  rw [factorialEnvelope_mul_labeledMass hs, ← ENNReal.ofReal_mul ha] at h
  have hlog := Real.log_natCast_nonneg n
  have hk := twoStablePairSizeKernel_nonneg n (u, v)
  have hn : 0 ≤ a * (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n (u, v)) := by
    positivity
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top h).trans_eq (ENNReal.toReal_ofReal hn)

private theorem scoreFixedOrientationPairEvent_le_labeledMass
    {R : ScoreProfile n → Matching n → Matching n → Prop} {u v : ℕ}
    (hs : ValidPairSizes n (u, v)) {P T : Multiset ℕ → Prop}
    (z : LabeledOrientationPairs n u v P T) :
    continuousScoreLaw n (scoreFixedOrientationPairEvent R z.val) ≤
      ENNReal.ofReal (labeledStablePairMassBound n u v) := by
  obtain ⟨hor, hu, hv, _, _⟩ := z.property
  apply measure_stablePairSector_le_labeledStablePairMassBound hs hor hu hv
  exact Eventually.of_forall fun _ hx ↦
    ⟨(scoreFixedOrientationPairEvent_data hx).1, (scoreFixedOrientationPairEvent_data hx).2.1,
      (scoreFixedOrientationPairEvent_data hx).2.2.1⟩

/-- The size-bin mass of any measurable subevent is bounded by the unrestricted kernel. -/
theorem scorePairSizeMass_toReal_le_kernel
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) {s : ℕ × ℕ} (hs : ValidPairSizes n s) :
    (scorePairSizeMass R s).toReal ≤
      Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s := by
  rcases s with ⟨u, v⟩
  have h := scorePairSizeMass_le_card_mul hR (u, v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ ⟨trivial, trivial⟩)
    (scoreFixedOrientationPairEvent_le_labeledMass hs)
  have hcount := card_labeledOrientationPairs_unrestricted_le hs.2.2
  have hmass := h.trans (mul_le_mul_left hcount _)
  exact (scorePairSizeMass_toReal_le_of_envelope hs (a := 1) zero_le_one
    (by simpa only [ENNReal.ofReal_one, one_mul] using hmass)).trans_eq (one_mul _)

/-- The forced-cycle exception multiplies the size-bin kernel by its cycle-type fraction bound. -/
theorem scorePairSizeMass_toReal_le_forced
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν}) {s : ℕ × ℕ} (hs : ValidPairSizes n s)
    {L : ℕ} (hL : 2 ≤ L) (hu : L ≤ s.1) (hlog : 100 ≤ Real.log (L : ℝ)) :
    (scorePairSizeMass (fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L) s).toReal ≤
      (400 / Real.log (L : ℝ)) *
        (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s) := by
  rcases s with ⟨u, v⟩
  let Q : ScoreProfile n → Matching n → Matching n → Prop :=
    fun x μ ν ↦ R x μ ν ∧ x ∈ forcedShortCycleException μ ν L
  have hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν} := fun μ ν ↦
    (hR μ ν).inter (measurableSet_forcedShortCycleException μ ν L)
  have hcycle := forcedCycleTypeCoverage_of_scoreForcedException (R := Q) L (fun _ _ ↦
    Eventually.of_forall fun _ hx ↦ hx.2.2.2.2)
  have h := scorePairSizeMass_le_card_mul hQ (u, v)
    (forcedShortCycleTypeException L) (fun _ ↦ True) hcycle
    (scoreFixedOrientationPairEvent_le_labeledMass hs)
  have hcount := card_labeledOrientationPairs_forcedShortException_le hs.2.2 hL hu hlog
  have hfactor : 0 ≤ (400 : ℝ) / Real.log (L : ℝ) := by
    exact div_nonneg (by norm_num) (by linarith)
  apply scorePairSizeMass_toReal_le_of_envelope hs hfactor
  exact (h.trans (mul_le_mul_left hcount _)).trans_eq (by ac_rfl)

/-- On finite regular sizes, the actual background size-bin mass pays `1200 / log L`. -/
theorem scorePairSizeMass_toReal_le_background_regular
    {L : ℕ} (hn : 0 < n) (hbudget : BackgroundCycleBudget n L)
    {R : ScoreProfile n → Matching n → Matching n → Prop}
    (hR : ∀ μ ν, MeasurableSet {x | R x μ ν})
    (hdom : ∀ x μ ν, R x μ ν → InResidualEndpointScoreDomain x ν)
    {s : ℕ × ℕ} (hs : ValidPairSizes n s) (hreg : RegularOrientationPair n L s) :
    (scorePairSizeMass
      (fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L) s).toReal ≤
      (1200 / Real.log (L : ℝ)) *
        (Real.exp 72 * (1 + Real.log n) * twoStablePairSizeKernel n s) := by
  rcases s with ⟨u, v⟩
  let Q : ScoreProfile n → Matching n → Matching n → Prop :=
    fun x μ ν ↦ R x μ ν ∧ x ∈ backgroundShortCycleException μ ν L
  have hQ : ∀ μ ν, MeasurableSet {x | Q x μ ν} := fun μ ν ↦
    (hR μ ν).inter (measurableSet_backgroundShortCycleException μ ν L)
  let a := (1200 : ℝ) / Real.log (L : ℝ)
  have hfixed (z : LabeledOrientationPairs n u v (fun _ ↦ True) (fun _ ↦ True)) :
      continuousScoreLaw n (scoreFixedOrientationPairEvent Q z.val) ≤
        ENNReal.ofReal a * ENNReal.ofReal (labeledStablePairMassBound n u v) := by
    obtain ⟨hor, hu, hv, _, _⟩ := z.property
    let E := scoreFixedOrientationPairEvent R z.val
    have hsub : scoreFixedOrientationPairEvent Q z.val ⊆ E ∩
        backgroundShortCycleException z.val.1.1 z.val.1.2 L := by
      intro x hx
      exact ⟨⟨⟨hx.1.1, hx.1.2.1, hx.1.2.2.1, hx.1.2.2.2.1⟩, hx.2⟩, hx.1.2.2.2.2⟩
    refine (measure_mono hsub).trans ?_
    have h := measure_backgroundException_le_labeledStablePairMassBound_regular hn hbudget hor
      (by simpa only [hu, hv] using hs)
      (by simpa only [hu, hv] using hreg) (E := E) (Eventually.of_forall fun _ hx ↦
        ⟨(scoreFixedOrientationPairEvent_data hx).1, (scoreFixedOrientationPairEvent_data hx).2.1,
          (scoreFixedOrientationPairEvent_data hx).2.2.1, hdom _ _ _ hx.1.2.2.2⟩)
    simpa only [hu, hv] using h
  have h := scorePairSizeMass_le_card_mul hQ (u, v) (fun _ ↦ True) (fun _ ↦ True)
    (fun _ _ ↦ Eventually.of_forall fun _ _ ↦ ⟨trivial, trivial⟩) hfixed
  have hcount := card_labeledOrientationPairs_unrestricted_le hs.2.2
  have ha : 0 ≤ a := div_nonneg (by norm_num) (by have := hbudget.log_cutoff; linarith)
  apply scorePairSizeMass_toReal_le_of_envelope hs ha
  exact (h.trans (mul_le_mul_left hcount _)).trans_eq (mul_left_comm _ _ _)

end LennonPittelFormalization
