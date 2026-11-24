module

public import LennonPittel.LennonPittelLowerTailCriterion

/-! # Centered-moment bounds for the closed lower tail -/

@[expose] public section

open Filter MeasureTheory StableMarriage
open scoped ENNReal Topology

namespace LennonPittelFormalization.Quantitative

/-- A lower bound for the random center controls the closed lower tail even when
the count has an atom exactly at the threshold. The domination need only hold a.e. -/
theorem measure_closedLowerTail_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {S T M : Ω → ℝ} (hTS : ∀ᵐ x ∂μ, T x ≤ S x) (hT : Measurable T) (hM : Measurable M)
    {a s d : ℝ} (ha : 0 < a) (hsd : s < d) :
    μ {x | S x ≤ s * a} ≤ μ {x | M x < d * a} +
      scaledCenteredCountMoment μ a T M / ENNReal.ofReal ((d - s) ^ 2) := by
  let f (x : Ω) := ENNReal.ofReal (((T x - M x) / a) ^ 2)
  let E := {x | ENNReal.ofReal ((d - s) ^ 2) ≤ f x}
  have hf : Measurable f := by unfold f; fun_prop
  have hpos : 0 < (d - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hsd)
  have hE : μ E ≤ scaledCenteredCountMoment μ a T M / ENNReal.ofReal ((d - s) ^ 2) :=
    meas_ge_le_lintegral_div hf.aemeasurable (ENNReal.ofReal_pos.mpr hpos).ne'
      ENNReal.ofReal_ne_top
  have hcover : {x | S x ≤ s * a} ≤ᵐ[μ] {x | M x < d * a} ∪ E := by
    filter_upwards [hTS] with x hx hsmall
    change S x ≤ s * a at hsmall
    by_cases hbad : M x < d * a
    · exact Or.inl hbad
    right
    have hdiff : d - s ≤ -((T x - M x) / a) := by
      have h : (T x - M x) / a ≤ -(d - s) := (div_le_iff₀ ha).mpr (by
        nlinarith only [hx, hsmall, le_of_not_gt hbad])
      linarith
    apply ENNReal.ofReal_le_ofReal
    calc
      (d - s) ^ 2 ≤ (-((T x - M x) / a)) ^ 2 :=
        pow_le_pow_left₀ (sub_pos.mpr hsd).le hdiff _
      _ = _ := by ring
  exact (measure_mono_ae hcover).trans ((measure_union_le _ _).trans (add_le_add le_rfl hE))

/-- Probability form with the same high-center hypothesis and centered moment as
the fixed-parameter variance proof. No upper bound on the failure budget is needed. -/
theorem measure_closedLowerTail_le_of_center {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {S T M : Ω → ℝ}
    (hTS : ∀ᵐ x ∂μ, T x ≤ S x) (hT : Measurable T) (hM : Measurable M)
    {a s d η : ℝ} (ha : 0 < a) (hsd : s < d) (hη : 0 ≤ η)
    (hcenter : ENNReal.ofReal (1 - η) ≤ μ {x | d * a ≤ M x}) :
    μ {x | S x ≤ s * a} ≤ ENNReal.ofReal η +
      scaledCenteredCountMoment μ a T M / ENNReal.ofReal ((d - s) ^ 2) := by
  have hm : MeasurableSet {x | d * a ≤ M x} := measurableSet_le measurable_const hM
  have hcompl : {x | M x < d * a} = {x | d * a ≤ M x}ᶜ := by ext x; simp
  have hbad : μ {x | M x < d * a} ≤ ENNReal.ofReal η := by
    rw [hcompl, measure_compl hm (measure_ne_top μ _), measure_univ]
    rw [ENNReal.ofReal_sub _ hη, ENNReal.ofReal_one, tsub_le_iff_right] at hcenter
    rw [tsub_le_iff_right, add_comm]
    exact hcenter
  exact (measure_closedLowerTail_le μ hTS hT hM ha hsd).trans (add_le_add hbad le_rfl)

/-- Transfer the same estimate to the actual finite independent uniform preference law. -/
theorem uniformProfile_closedLowerTail_le {n : ℕ} {T M : ScoreProfile n → ℝ}
    (hTS : ∀ᵐ x ∂continuousScoreLaw n, T x ≤ (numStableMatchings (profileOfScores x) : ℝ))
    (hT : Measurable T) (hM : Measurable M) {a s d η : ℝ}
    (ha : 0 < a) (hsd : s < d) (hη : 0 ≤ η)
    (hcenter : ENNReal.ofReal (1 - η) ≤ continuousScoreLaw n {x | d * a ≤ M x}) :
    (uniformProfile n).toMeasure {p | (numStableMatchings p : ℝ) ≤ s * a} ≤ ENNReal.ofReal η +
      scaledCenteredCountMoment (continuousScoreLaw n) a T M / ENNReal.ofReal ((d - s) ^ 2) := by
  let G : Set (Profile n) := {p | (numStableMatchings p : ℝ) ≤ s * a}
  change (uniformProfile n).toMeasure G ≤ _
  rw [← (measurePreserving_profileOfScores n).map_eq,
    Measure.map_apply (measurePreserving_profileOfScores n).measurable
      (show MeasurableSet G from MeasurableSet.of_discrete)]
  exact measure_closedLowerTail_le_of_center _ hTS hT hM ha hsd hη hcenter

/-- A fixed positive threshold gap and vanishing variance suffice. Both inputs
allow arbitrary eventual slack; their starting indices can depend on that slack. -/
theorem limsup_uniformProfile_closedLowerTail_le {T M : ∀ n, ScoreProfile n → ℝ}
    (hT : ∀ n, Measurable (T n)) (hM : ∀ n, Measurable (M n))
    (hTS : ∀ᶠ n : ℕ in atTop, ∀ᵐ x ∂continuousScoreLaw n,
      T n x ≤ (numStableMatchings (profileOfScores x) : ℝ))
    {a : ℕ → ℝ} (ha : ∀ᶠ n in atTop, 0 < a n)
    {s d η : ℝ} (hsd : s < d) (hη : 0 ≤ η)
    (hcenter : ∀ δ : ℝ, 0 < δ → ∀ᶠ n : ℕ in atTop,
      ENNReal.ofReal (1 - (η + δ)) ≤ continuousScoreLaw n {x | d * a n ≤ M n x})
    (hmoment : ∀ e : ℝ, 0 < e → ∀ᶠ n : ℕ in atTop,
      scaledCenteredCountMoment (continuousScoreLaw n) (a n) (T n) (M n) ≤ ENNReal.ofReal e) :
    limsup (fun n : ℕ ↦ (uniformProfile n).toMeasure
      {p | (numStableMatchings p : ℝ) ≤ s * a n}) atTop ≤ ENNReal.ofReal η := by
  have hlim : Tendsto (fun δ : ℝ ↦ ENNReal.ofReal (η + 2 * δ))
      (𝓝[>] (0 : ℝ)) (𝓝 (ENNReal.ofReal η)) := by
    apply ENNReal.continuous_ofReal.continuousAt.tendsto.comp
    simpa using (tendsto_const_nhds (x := η)).add
      (tendsto_const_nhds (x := (2 : ℝ)) |>.mul
        (tendsto_id.mono_left (nhdsWithin_le_nhds (a := (0 : ℝ)) (s := Set.Ioi 0))))
  apply ge_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (0 : ℝ)) (a := 0)] with δ hδ
  have hδ' : 0 < δ := hδ
  have hgap : 0 < (d - s) ^ 2 := sq_pos_of_pos (sub_pos.mpr hsd)
  apply limsup_le_of_le (by isBoundedDefault)
  filter_upwards [hTS, ha, hcenter δ hδ', hmoment _ (mul_pos hδ' hgap)]
    with n hTSn han hcenter_n hmoment_n
  refine (uniformProfile_closedLowerTail_le hTSn (hT n) (hM n) han hsd
    (add_nonneg hη hδ'.le) hcenter_n).trans ?_
  have hvar : scaledCenteredCountMoment (continuousScoreLaw n) (a n) (T n) (M n) /
      ENNReal.ofReal ((d - s) ^ 2) ≤ ENNReal.ofReal δ := by
    refine (ENNReal.div_le_div_right hmoment_n _).trans_eq ?_
    rw [← ENNReal.ofReal_div_of_pos hgap, mul_div_cancel_right₀ _ hgap.ne']
  refine (add_le_add le_rfl hvar).trans_eq ?_
  rw [← ENNReal.ofReal_add (add_nonneg hη hδ'.le) hδ'.le]
  congr 1
  ring

end LennonPittelFormalization.Quantitative
