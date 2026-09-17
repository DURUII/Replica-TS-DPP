import TSDPP.BetaGamma

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

/-! ## Auxiliary measure facts

Mathlib has no support lemma for `gammaMeasure` beyond its definition, so the facts used below
are extracted here from `gammaMeasure a r = volume.withDensity (gammaPDF a r)`. -/

/-- Instance search does not unfold the `noncomputable def gammaMeasure`, so `SFinite` — which
`Measure.prod_prod` needs for the second factor — has to be supplied by hand. -/
instance instSFiniteGammaMeasure (a r : ℝ) : SFinite (gammaMeasure a r) := by
  rw [gammaMeasure]
  infer_instance

private lemma setLIntegral_of_volume_eq_zero {s : Set ℝ} (hs : volume s = 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = 0 := by
  rw [Measure.restrict_eq_zero.mpr hs, lintegral_zero_measure]

private lemma gammaMeasure_Iio_zero (a r : ℝ) : gammaMeasure a r (Set.Iio 0) = 0 := by
  rw [gammaMeasure, withDensity_apply _ measurableSet_Iio]
  exact setLIntegral_eq_zero measurableSet_Iio fun _ hx => gammaPDF_of_neg hx

private lemma gammaMeasure_singleton_zero (a r x : ℝ) : gammaMeasure a r {x} = 0 := by
  rw [gammaMeasure, withDensity_apply _ (measurableSet_singleton x)]
  exact setLIntegral_of_volume_eq_zero Real.volume_singleton _

private lemma betaMeasure_Iio_zero (a b : ℝ) : betaMeasure a b (Set.Iio (0 : ℝ)) = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Iio]
  exact setLIntegral_eq_zero measurableSet_Iio fun _ hx => betaPDF_eq_zero_of_nonpos hx.le

private lemma betaMeasure_Ici_one_zero (a b : ℝ) : betaMeasure a b (Set.Ici (1 : ℝ)) = 0 := by
  rw [betaMeasure, withDensity_apply _ measurableSet_Ici]
  exact setLIntegral_eq_zero measurableSet_Ici fun _ hx => betaPDF_eq_zero_of_one_le hx

/-! ## The two sets the argument turns on -/

/-- The set on which the ratio map is well behaved: both coordinates nonnegative and a positive
sum. -/
private def goodSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 ≤ p.1 ∧ 0 ≤ p.2 ∧ 0 < p.1 + p.2}

/-- The complement of `goodSet`, written as the union of a horizontal half-plane, a vertical
half-plane and the origin.  Each piece is null for the product of two Gamma laws. -/
private def badSet : Set (ℝ × ℝ) :=
  {p : ℝ × ℝ | p.1 < 0} ∪ {p : ℝ × ℝ | p.2 < 0} ∪ {p : ℝ × ℝ | p = (0, 0)}

private lemma compl_goodSet_subset_badSet : goodSetᶜ ⊆ badSet := by
  intro p hp
  by_cases h1 : p.1 < 0
  · exact Or.inl (Or.inl h1)
  · by_cases h2 : p.2 < 0
    · exact Or.inl (Or.inr h2)
    · refine Or.inr ?_
      push Not at h1 h2
      have hsum : ¬ 0 < p.1 + p.2 := fun hc => hp ⟨h1, h2, hc⟩
      have hsle : p.1 + p.2 ≤ 0 := not_lt.mp hsum
      exact Prod.ext (le_antisymm (by linarith) h1) (le_antisymm (by linarith) h2)

private lemma goodSet_of_not_badSet {p : ℝ × ℝ} (hp : p ∉ badSet) : p ∈ goodSet := by
  by_contra hg
  exact hp (compl_goodSet_subset_badSet hg)

/-- Off `badSet` — that is, on `goodSet` — membership of the ratio in `Ici t` is exactly the
linear inequality `t * p.2 ≤ (1 - t) * p.1`.  This single identity removes all case analysis on
`t` from the main proof. -/
private lemma ratio_mem_Ici_iff {t : ℝ} {p : ℝ × ℝ} (hp : p ∈ goodSet) :
    p.1 / (p.1 + p.2) ∈ Set.Ici t ↔ t * p.2 ≤ (1 - t) * p.1 := by
  simp only [goodSet, Set.mem_ofPred_eq] at hp
  have hsum : 0 < p.1 + p.2 := hp.2.2
  rw [Set.mem_Ici, le_div_iff₀ hsum]
  constructor <;> intro h <;> linarith

/-! ## The null sets -/

private lemma prod_badSet_zero {α β : ℝ} :
    ((gammaMeasure α 1).prod (gammaMeasure β 1)) badSet = 0 := by
  have h1 : ((gammaMeasure α 1).prod (gammaMeasure β 1)) {p : ℝ × ℝ | p.1 < 0} = 0 := by
    have hrect : {p : ℝ × ℝ | p.1 < 0} = Set.Iio (0 : ℝ) ×ˢ Set.univ := by ext p; simp
    rw [hrect, Measure.prod_prod, gammaMeasure_Iio_zero, zero_mul]
  have h2 : ((gammaMeasure α 1).prod (gammaMeasure β 1)) {p : ℝ × ℝ | p.2 < 0} = 0 := by
    have hrect : {p : ℝ × ℝ | p.2 < 0} = Set.univ ×ˢ Set.Iio (0 : ℝ) := by ext p; simp
    rw [hrect, Measure.prod_prod, gammaMeasure_Iio_zero, mul_zero]
  have h3 : ((gammaMeasure α 1).prod (gammaMeasure β 1)) {p : ℝ × ℝ | p = (0, 0)} = 0 := by
    have hrect : {p : ℝ × ℝ | p = (0, 0)} = ({0} : Set ℝ) ×ˢ ({0} : Set ℝ) := by
      ext p; simp [Prod.ext_iff]
    rw [hrect, Measure.prod_prod, gammaMeasure_singleton_zero, zero_mul]
  show ((gammaMeasure α 1).prod (gammaMeasure β 1))
      ({p : ℝ × ℝ | p.1 < 0} ∪ {p : ℝ × ℝ | p.2 < 0} ∪ {p : ℝ × ℝ | p = (0, 0)}) = 0
  rw [measure_union_null_iff, measure_union_null_iff]
  exact ⟨⟨h1, h2⟩, h3⟩

private lemma prod_snd_zero {α β : ℝ} :
    ((gammaMeasure α 1).prod (gammaMeasure β 1)) {p : ℝ × ℝ | p.2 = 0} = 0 := by
  have hrect : {p : ℝ × ℝ | p.2 = 0} = Set.univ ×ˢ ({0} : Set ℝ) := by ext p; simp
  rw [hrect, Measure.prod_prod, gammaMeasure_singleton_zero, mul_zero]

private lemma prod_goodSet_eq_one {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    ((gammaMeasure α 1).prod (gammaMeasure β 1)) goodSet = 1 := by
  have hα' : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hβ' : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  have h0 : ((gammaMeasure α 1).prod (gammaMeasure β 1)) goodSetᶜ = 0 :=
    measure_mono_null compl_goodSet_subset_badSet (prod_badSet_zero (α := α) (β := β))
  have h : goodSet =ᵐ[((gammaMeasure α 1).prod (gammaMeasure β 1))] Set.univ :=
    ae_eq_univ.mpr h0
  rw [measure_congr h, measure_univ]

/-- Map-level Beta–Gamma ratio law: the law of `G_a/(G_a+G_b)` for independent
`G_a ~ Gamma(a,1)`, `G_b ~ Gamma(b,1)` is `Beta(a,b)`. -/
theorem gamma_ratio_isBetaMeasure {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
      (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) := by
  have hP : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  have hGα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hGβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  have hfm : Measurable fun p : ℝ × ℝ => p.1 / (p.1 + p.2) := by fun_prop
  refine Measure.ext_of_Ici (betaMeasure α β)
    (((gammaMeasure α 1).prod (gammaMeasure β 1)).map fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ?_
  intro t
  rw [Measure.map_apply hfm measurableSet_Ici]
  by_cases ht0 : 0 < t
  · by_cases ht1 : t < 1
    · -- `0 < t < 1`: the set-level ratio law applies verbatim.
      have hae : (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t
          =ᵐ[((gammaMeasure α 1).prod (gammaMeasure β 1))]
            {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1} := by
        rw [ae_eq_set]
        refine ⟨?_, ?_⟩
        · refine measure_mono_null (fun p hp => ?_) (prod_badSet_zero (α := α) (β := β))
          by_contra hb
          have hG := goodSet_of_not_badSet hb
          simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq] at hp
          exact hp.2 ((ratio_mem_Ici_iff hG).mp hp.1)
        · refine measure_mono_null (fun p hp => ?_) (prod_badSet_zero (α := α) (β := β))
          by_contra hb
          have hG := goodSet_of_not_badSet hb
          simp only [Set.mem_sdiff, Set.mem_preimage, Set.mem_Ici, Set.mem_ofPred_eq] at hp
          exact hp.2 ((ratio_mem_Ici_iff hG).mpr hp.1)
      rw [measure_congr hae]
      exact (gammaMeasure_prod_ratio hα hβ ht0 ht1).symm
    · -- `1 ≤ t`: the ratio is `≤ 1` on `goodSet`, so the event is confined to `{p.2 = 0} ∪ badSet`.
      have ht : (1 : ℝ) ≤ t := not_lt.mp ht1
      have hB : betaMeasure α β (Set.Ici t) = 0 :=
        measure_mono_null (Set.Ici_subset_Ici.mpr ht) (betaMeasure_Ici_one_zero α β)
      have hsub : (fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t
          ⊆ {p : ℝ × ℝ | p.2 = 0} ∪ badSet := by
        intro p hp
        by_cases hb : p ∈ badSet
        · exact Or.inr hb
        · refine Or.inl ?_
          have hG := goodSet_of_not_badSet hb
          simp only [goodSet, Set.mem_ofPred_eq] at hG
          simp only [Set.mem_preimage, Set.mem_Ici] at hp
          have h1 : (1 : ℝ) ≤ p.1 / (p.1 + p.2) := le_trans ht hp
          have h2 : p.1 + p.2 ≤ p.1 := by simpa using (le_div_iff₀ hG.2.2).mp h1
          have h3 : 0 ≤ p.2 := hG.2.1
          have h4 : p.2 ≤ 0 := by linarith
          exact le_antisymm h4 h3
      have hbound : ((gammaMeasure α 1).prod (gammaMeasure β 1))
          ({p : ℝ × ℝ | p.2 = 0} ∪ badSet) = 0 := by
        have hle : ((gammaMeasure α 1).prod (gammaMeasure β 1))
            ({p : ℝ × ℝ | p.2 = 0} ∪ badSet)
            ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1)) ({p : ℝ × ℝ | p.2 = 0})
              + ((gammaMeasure α 1).prod (gammaMeasure β 1)) badSet := measure_union_le _ _
        rw [prod_snd_zero, prod_badSet_zero, add_zero] at hle
        exact le_antisymm hle bot_le
      have hR : ((gammaMeasure α 1).prod (gammaMeasure β 1))
          ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t) = 0 :=
        measure_mono_null hsub hbound
      rw [hB, hR]
  · -- `t ≤ 0`: both sides take the value `1`; the ratio is nonnegative on `goodSet`.
    have ht : t ≤ 0 := not_lt.mp ht0
    have hB : betaMeasure α β (Set.Ici t) = 1 := by
      have h0 : betaMeasure α β (Set.Ici (0 : ℝ)) = 1 := by
        have hz : betaMeasure α β (Set.Iio (0 : ℝ)) = 0 := betaMeasure_Iio_zero α β
        have hdisj : Disjoint (Set.Ici (0 : ℝ)) (Set.Iio (0 : ℝ)) := by
          rw [Set.disjoint_left]
          intro x hx1 hx2
          simp only [Set.mem_Ici] at hx1
          simp only [Set.mem_Iio] at hx2
          linarith
        rw [← measure_univ (μ := betaMeasure α β), ← Set.Ici_union_Iio (a := (0 : ℝ)),
          measure_union hdisj measurableSet_Iio, hz, add_zero]
      refine le_antisymm ?_ ?_
      · exact (measure_mono (Set.subset_univ _)).trans (le_of_eq measure_univ)
      · calc (1 : ℝ≥0∞) = betaMeasure α β (Set.Ici (0 : ℝ)) := h0.symm
          _ ≤ betaMeasure α β (Set.Ici t) := measure_mono (Set.Ici_subset_Ici.mpr ht)
    have hR : ((gammaMeasure α 1).prod (gammaMeasure β 1))
        ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t) = 1 := by
      refine le_antisymm ?_ ?_
      · exact (measure_mono (Set.subset_univ _)).trans (le_of_eq measure_univ)
      · calc (1 : ℝ≥0∞)
            = ((gammaMeasure α 1).prod (gammaMeasure β 1)) goodSet :=
              (prod_goodSet_eq_one hα hβ).symm
          _ ≤ ((gammaMeasure α 1).prod (gammaMeasure β 1))
                ((fun p : ℝ × ℝ => p.1 / (p.1 + p.2)) ⁻¹' Set.Ici t) :=
              measure_mono fun _ hp => by
                simp only [goodSet, Set.mem_ofPred_eq] at hp
                simp only [Set.mem_preimage, Set.mem_Ici]
                exact le_trans ht (div_nonneg hp.1 (le_of_lt hp.2.2))
    rw [hB, hR]

end TSDPP
