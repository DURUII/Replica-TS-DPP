import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

private lemma setLIntegral_of_measure_eq_zero {s : Set ℝ} (hs : volume s = 0) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = 0 := by
  rw [Measure.restrict_eq_zero.mpr hs, lintegral_zero_measure]

private lemma lintegral_sub_right (c : ℝ) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (y - c) = ∫⁻ y, h y := by
  have h1 : ∫⁻ y, h y ∂Measure.map (fun y : ℝ => y + (-c)) volume = ∫⁻ y, h (y + (-c)) :=
    lintegral_map hmeas (by fun_prop)
  rw [map_add_right_eq_self volume (-c)] at h1
  simpa [sub_eq_add_neg] using h1.symm

private lemma lintegral_mul_left_of_pos {c : ℝ} (hc : 0 < c) {h : ℝ → ℝ≥0∞} (hmeas : Measurable h) :
    ∫⁻ y, h (c * y) = ENNReal.ofReal c⁻¹ * ∫⁻ y, h y := by
  have h1 : ∫⁻ y, h y ∂Measure.map (fun y : ℝ => c * y) volume = ∫⁻ y, h (c * y) :=
    lintegral_map hmeas (by fun_prop)
  rw [Real.map_volume_mul_left (ne_of_gt hc), lintegral_smul_measure,
    abs_of_pos (inv_pos.mpr hc), smul_eq_mul] at h1
  exact h1.symm

private lemma lintegral_rpow_exp_neg_Ioi (a : ℝ) (ha : 0 < a) :
    ∫⁻ u in Set.Ioi (0 : ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u))
      = ENNReal.ofReal (Real.Gamma a) := by
  have hInt : ∫ u in Set.Ioi (0 : ℝ), u ^ (a - 1) * Real.exp (-u) = Real.Gamma a := by
    simpa only [one_mul, one_div_one, Real.one_rpow] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := 1) ha one_pos
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0 : ℝ))]
      fun u : ℝ => u ^ (a - 1) * Real.exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
  have hcont : AEStronglyMeasurable (fun u : ℝ => u ^ (a - 1) * Real.exp (-u))
      (volume.restrict (Set.Ioi (0 : ℝ))) := by fun_prop
  have h := integral_eq_lintegral_of_nonneg_ae hnonneg hcont
  rw [hInt] at h
  have htop : (∫⁻ u, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u))
      ∂(volume.restrict (Set.Ioi (0 : ℝ)))) ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.toReal_top] at h
    exact (Real.Gamma_pos_of_pos ha).ne' h
  rw [← ENNReal.ofReal_toReal htop, h.symm]

/-- Reflection: `r ↦ 1 - r` preserves Lebesgue measure. -/
private lemma lintegral_one_sub {f : ℝ → ℝ≥0∞} (hmeas : Measurable f) :
    ∫⁻ r, f (1 - r) = ∫⁻ r, f r := by
  have hmap : Measure.map (fun r : ℝ => 1 - r) volume = volume := by
    have hcomp : (fun r : ℝ => 1 - r) = (fun u : ℝ => 1 + u) ∘ (fun r : ℝ => -r) := rfl
    rw [hcomp, ← Measure.map_map (g := fun u : ℝ => 1 + u) (f := fun r : ℝ => -r)
      (by fun_prop) (by fun_prop)]
    rw [Measure.map_neg_eq_self (volume : Measure ℝ), map_add_left_eq_self]
  have h1 := lintegral_map (μ := volume) (f := f) (g := fun r : ℝ => 1 - r) hmeas
    (by fun_prop)
  rw [hmap] at h1
  exact h1.symm

/-- The set version of reflection. -/
private lemma setLIntegral_one_sub (s : Set ℝ) (hs : MeasurableSet s) {f : ℝ → ℝ≥0∞}
    (hmeas : Measurable f) :
    ∫⁻ r in s, f r = ∫⁻ w in (fun r : ℝ => 1 - r) ⁻¹' s, f (1 - w) := by
  have h : ∫⁻ r, s.indicator f (1 - r) = ∫⁻ r in s, f r := by
    rw [lintegral_one_sub (hmeas.indicator hs), lintegral_indicator hs]
  have h2 : ∫⁻ r, s.indicator f (1 - r)
      = ∫⁻ w in (fun r : ℝ => 1 - r) ⁻¹' s, f (1 - w) := by
    rw [← lintegral_indicator (hs.preimage (by fun_prop)) (fun w => f (1 - w))]
    refine lintegral_congr fun w => ?_
    by_cases hw : (1 - w) ∈ s
    · rw [Set.indicator_of_mem hw,
        Set.indicator_of_mem (show w ∈ (fun r : ℝ => 1 - r) ⁻¹' s from hw)]
    · rw [Set.indicator_of_notMem hw,
        Set.indicator_of_notMem (show w ∉ (fun r : ℝ => 1 - r) ⁻¹' s from hw)]
  exact h.symm.trans h2

/-- The set version of reflection, with the preimage set given explicitly. -/
private lemma setLIntegral_one_sub' {s t : Set ℝ} (hs : MeasurableSet s) {f : ℝ → ℝ≥0∞}
    (hmeas : Measurable f) (hst : (fun r : ℝ => 1 - r) ⁻¹' s = t) :
    ∫⁻ r in s, f r = ∫⁻ w in t, f (1 - w) := by
  rw [setLIntegral_one_sub s hs hmeas, hst]

/-- Two sets that differ only in a single point have the same set integral. -/
private lemma setLIntegral_congr_of_diff_subset_singleton {s t : Set ℝ} {c : ℝ}
    (h : s \ t ⊆ {c}) (h' : t \ s ⊆ {c}) (f : ℝ → ℝ≥0∞) :
    ∫⁻ x in s, f x = ∫⁻ x in t, f x := by
  apply setLIntegral_congr
  rw [ae_eq_set]
  exact ⟨measure_mono_null h Real.volume_singleton,
    measure_mono_null h' Real.volume_singleton⟩

/-- Pointwise algebra for the Gamma-ratio computation. -/
private theorem gammaPDF_mul_factor (a b r u : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hu : 0 < u) (hr : 0 < r) (hr1 : r < 1) :
    ENNReal.ofReal u * (gammaPDF a 1 (u - u * r) * gammaPDF b 1 (u * r))
      = ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b))
        * ENNReal.ofReal (u ^ (a + b - 1) * Real.exp (-u)) := by
  have h3 : 0 ≤ u - u * r := by
    have h : u - u * r = u * (1 - r) := by ring
    rw [h]
    exact mul_nonneg hu.le (by linarith)
  have h4 : 0 ≤ u * r := mul_nonneg hu.le hr.le
  have hA1 : 0 ≤ (u - u * r) ^ (a - 1) * Real.exp (-(u - u * r)) / Real.Gamma a :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg h3 _) (Real.exp_nonneg _)) (by positivity)
  have hA2 : 0 ≤ (u * r) ^ (b - 1) * Real.exp (-(u * r)) / Real.Gamma b :=
    div_nonneg (mul_nonneg (Real.rpow_nonneg h4 _) (Real.exp_nonneg _)) (by positivity)
  have hT : 0 ≤ u ^ (a + b - 1) * Real.exp (-u) :=
    mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
  have hg1 : gammaPDF a 1 (u - u * r)
      = ENNReal.ofReal ((u - u * r) ^ (a - 1) * Real.exp (-(u - u * r)) / Real.Gamma a) := by
    rw [gammaPDF_of_nonneg h3, Real.one_rpow, one_mul]
    congr 1
    ring
  have hg2 : gammaPDF b 1 (u * r)
      = ENNReal.ofReal ((u * r) ^ (b - 1) * Real.exp (-(u * r)) / Real.Gamma b) := by
    rw [gammaPDF_of_nonneg h4, Real.one_rpow, one_mul]
    congr 1
    ring
  have h1r : (0 : ℝ) ≤ 1 - r := by linarith
  have hpow : u ^ (a + b - 1) = u * u ^ (a - 1) * u ^ (b - 1) := by
    have hA : u ^ (a + b - 1) = u ^ a * u ^ (b - 1) := by
      conv_lhs => rw [show a + b - 1 = a + (b - 1) by ring]
      rw [Real.rpow_add hu]
    have hB : u ^ a = u * u ^ (a - 1) := by
      conv_lhs => rw [show a = 1 + (a - 1) by ring]
      rw [Real.rpow_add hu, Real.rpow_one]
    rw [hA, hB]
  have hexp : Real.exp (-u) = Real.exp (-(u * (1 - r))) * Real.exp (-(u * r)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [hg1, hg2, ← ENNReal.ofReal_mul hA1, ← ENNReal.ofReal_mul hu.le,
    ← ENNReal.ofReal_mul' hT]
  congr 1
  rw [show u - u * r = u * (1 - r) by ring]
  rw [Real.mul_rpow hu.le h1r]
  rw [Real.mul_rpow hu.le hr.le]
  rw [hpow, hexp]
  ring

/-- The Beta law of the upper tail: for `0 < a`, `0 < b`, `0 < t < 1`,
`β_{a,b}(Ici t) = ofReal (Γ(a+b)/(Γa Γb)) * ∫⁻ w in Icc t 1, ofReal (w^(a-1) * (1-w)^(b-1))`. -/
private theorem betaMeasure_Ici (a b t : ℝ) (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    betaMeasure a b (Ici t)
      = ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
        * ∫⁻ w in Set.Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
  have hc : 0 ≤ (1 : ℝ) / beta a b := le_of_lt (one_div_pos.mpr (beta_pos ha hb))
  have hg : Measurable fun w : ℝ => ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    fun_prop
  have hconst : (1 : ℝ) / beta a b = Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b) := by
    simp only [beta, one_div, inv_div]
  have hdisj₁ : Disjoint (Set.Ico t 1) (Set.Ici (1 : ℝ)) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ico] at hx1
    simp only [Set.mem_Ici] at hx2
    linarith
  have hdisj₂ : Disjoint (Set.Ico t 1) ({1} : Set ℝ) := by
    rw [Set.disjoint_left]
    intro x hx1 hx2
    simp only [Set.mem_Ico] at hx1
    simp only [Set.mem_singleton_iff] at hx2
    linarith
  rw [betaMeasure, withDensity_apply _ measurableSet_Ici]
  have hIci : ∫⁻ w in Set.Ici t, betaPDF a b w = ∫⁻ w in Set.Ico t 1, betaPDF a b w := by
    rw [← Set.Ico_union_Ici_eq_Ici ht1.le,
      lintegral_union measurableSet_Ici hdisj₁,
      show ∫⁻ w in Set.Ici (1 : ℝ), betaPDF a b w = 0 from
        setLIntegral_eq_zero measurableSet_Ici (fun x hx => betaPDF_eq_zero_of_one_le hx),
      add_zero]
  rw [hIci]
  have hsplit : ∫⁻ w in Set.Ico t 1, betaPDF a b w
      = ∫⁻ w in Set.Ico t 1,
          ENNReal.ofReal (1 / beta a b) * ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ico (fun x hx => ?_)
    rw [betaPDF_of_pos_lt_one (by linarith [hx.1]) hx.2, mul_assoc, ENNReal.ofReal_mul hc]
  rw [hsplit]
  rw [lintegral_const_mul (ENNReal.ofReal (1 / beta a b)) hg]
  have hIcoIcc : ∫⁻ w in Set.Ico t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1))
      = ∫⁻ w in Set.Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    rw [← Set.Ico_union_right ht1.le,
      lintegral_union (measurableSet_singleton 1) hdisj₂,
      show ∫⁻ w in ({1} : Set ℝ), ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) = 0 from by
        simp [Measure.restrict_eq_zero.mpr Real.volume_singleton],
      add_zero]
  rw [hIcoIcc, hconst]

/-- **Law of the Gamma ratio.**  For `0 < a`, `0 < b`, the ratio `G_a / (G_a + G_b)` of two
independent `Gamma(a,1)`, `Gamma(b,1)` variables has law `Beta(a,b)`, stated as a CDF identity:
`Pr(t ≤ G_a/(G_a+G_b)) = Pr_{Beta(a,b)}(Ici t)`. -/
theorem gammaMeasure_prod_ratio {a b t : ℝ} (ha : 0 < a) (hb : 0 < b)
    (ht0 : 0 < t) (ht1 : t < 1) :
    (gammaMeasure a 1).prod (gammaMeasure b 1) {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}
      = betaMeasure a b (Ici t) := by
  let A : Set (ℝ × ℝ) := {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}
  let F : ℝ × ℝ → ℝ≥0∞ := fun p => gammaPDF a 1 p.1 * gammaPDF b 1 p.2
  let G : ℝ → ℝ → ℝ≥0∞ := fun u y => A.indicator F (u - y, y)
  let K : ℝ → ℝ → ℝ≥0∞ := fun u r =>
    if 0 < r ∧ r ≤ 1 - t then gammaPDF a 1 (u - u * r) * gammaPDF b 1 (u * r) else 0
  change (gammaMeasure a 1).prod (gammaMeasure b 1) A = betaMeasure a b (Ici t)
  have hA : MeasurableSet A := by
    dsimp only [A]
    exact measurableSet_le (measurable_const.mul measurable_snd)
      (measurable_const.mul measurable_fst)
  have hFm : Measurable F := by
    dsimp only [F]
    exact ((measurable_gammaPDFReal a 1).ennreal_ofReal.comp measurable_fst).mul
      ((measurable_gammaPDFReal b 1).ennreal_ofReal.comp measurable_snd)
  have hga : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  have hgb : Measurable (gammaPDF b 1) := (measurable_gammaPDFReal b 1).ennreal_ofReal
  simp only [gammaMeasure]
  rw [MeasureTheory.prod_withDensity hga hgb, withDensity_apply _ hA]
  rw [← lintegral_indicator hA F]
  rw [lintegral_prod_symm _ (hFm.indicator hA).aemeasurable]
  -- goal : ∫⁻ y, ∫⁻ x, A.indicator F (x, y) = betaMeasure a b (Ici t)
  have h3 : ∫⁻ y, ∫⁻ x, A.indicator F (x, y) = ∫⁻ y, ∫⁻ u, G u y := by
    refine lintegral_congr fun y => ?_
    have hm : Measurable (fun x : ℝ => A.indicator F (x, y)) :=
      (hFm.indicator hA).comp (measurable_prodMk_right (y := y))
    exact (lintegral_sub_right y hm).symm
  rw [h3]
  -- goal : ∫⁻ y, ∫⁻ u, G u y = betaMeasure a b (Ici t)
  have h4 : ∫⁻ y, ∫⁻ u, G u y = ∫⁻ u, ∫⁻ y, G u y := by
    rw [lintegral_lintegral_swap (f := fun y u : ℝ => G u y)
      (show AEMeasurable (Function.uncurry (fun y u : ℝ => G u y))
          (volume.prod volume) from by
        apply Measurable.aemeasurable
        have hmk : Measurable (fun p : ℝ × ℝ => (p.2 - p.1, p.1)) := by fun_prop
        exact (hFm.indicator hA).comp hmk)]
  rw [h4]
  -- goal : ∫⁻ u, ∫⁻ y, G u y = betaMeasure a b (Ici t)
  have hG0 : ∀ u ∈ Iio (0 : ℝ), (∫⁻ y, G u y) = 0 := by
    intro u hu
    simp only [Set.mem_Iio] at hu
    have hz : (fun y : ℝ => G u y) = fun _ => 0 := by
      funext y
      by_cases hy : t * y ≤ (1 - t) * (u - y)
      · rw [show G u y = A.indicator F (u - y, y) from rfl,
          Set.indicator_of_mem (show (u - y, y) ∈ A from hy), show F (u - y, y)
            = gammaPDF a 1 (u - y) * gammaPDF b 1 y from rfl,
          gammaPDF_of_neg (show y < 0 by nlinarith [ht1, hu, hy]), mul_zero]
      · rw [show G u y = A.indicator F (u - y, y) from rfl,
          Set.indicator_of_notMem (show (u - y, y) ∉ A from hy)]
    rw [show (fun y : ℝ => G u y) = fun _ => (0 : ℝ≥0∞) from hz]
    exact lintegral_zero
  have hIio : ∫⁻ u in Iio (0 : ℝ), ∫⁻ y, G u y = 0 := by
    rw [show (∫⁻ u in Iio (0 : ℝ), ∫⁻ y, G u y)
        = ∫⁻ _u in Iio (0 : ℝ), (0 : ℝ≥0∞) from
      setLIntegral_congr_fun measurableSet_Iio hG0]
    exact lintegral_zero
  have hIic : ∫⁻ u in Iic (0 : ℝ), ∫⁻ y, G u y = 0 := by
    rw [← Set.Iio_union_Icc_eq_Iic (le_refl (0 : ℝ)), Set.Icc_self,
      lintegral_union (measurableSet_singleton 0) (by
        rw [Set.disjoint_left]
        intro x hx1 hx2
        simp only [Set.mem_Iio] at hx1
        simp only [Set.mem_singleton_iff] at hx2
        linarith)]
    rw [hIio, setLIntegral_of_measure_eq_zero Real.volume_singleton, add_zero]
  have h5b : ∫⁻ u, ∫⁻ y, G u y = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ y, G u y := by
    rw [← lintegral_add_compl (fun u : ℝ => ∫⁻ y, G u y) measurableSet_Ioi,
      Set.compl_Ioi, hIic, add_zero]

  -- ### Step 5c : for `u > 0`, substitute `y = u * r`
  have hKr : ∀ u : ℝ, Measurable (fun r : ℝ => K u r) := by
    intro u
    dsimp only [K]
    apply Measurable.ite
    · exact (measurableSet_lt measurable_const measurable_id).inter
        (measurableSet_le measurable_id measurable_const)
    · exact (((measurable_gammaPDFReal a 1).ennreal_ofReal.comp
          (measurable_const.sub (measurable_const.mul measurable_id))).mul
        ((measurable_gammaPDFReal b 1).ennreal_ofReal.comp
          (measurable_const.mul measurable_id)))
    · exact measurable_const
  have hKfull : ∀ u : ℝ, (∫⁻ r in Ioi (0 : ℝ), K u r) = ∫⁻ r, K u r := by
    intro u
    rw [show (∫⁻ r in Ioi (0 : ℝ), K u r)
        = ∫⁻ r, (Ioi (0 : ℝ)).indicator (fun r => K u r) r from
      (lintegral_indicator measurableSet_Ioi (fun r => K u r)).symm]
    refine lintegral_congr fun r => ?_
    by_cases hr : 0 < r
    · exact Set.indicator_of_mem hr _
    · have h0 : K u r = 0 := by
        dsimp only [K]
        exact ite_eq_right (by rintro ⟨h, -⟩; exact hr h)
      exact (Set.indicator_of_notMem hr _).trans h0.symm
  have h5c : ∀ u ∈ Ioi (0 : ℝ), (∫⁻ y, G u y)
      = ENNReal.ofReal u * ∫⁻ r, K u r := by
    intro u hu
    simp only [Set.mem_Ioi] at hu
    have hHm : Measurable (fun y : ℝ => G u y) := by
      have : Measurable (fun y : ℝ => (u - y, y)) := by fun_prop
      exact (hFm.indicator hA).comp this
    have hlin := lintegral_mul_left_of_pos hu hHm
    have hsub : ∫⁻ r in (Ioi (0 : ℝ))ᶜ, G u (u * r) = 0 := by
      rw [Set.compl_Ioi, ← lintegral_indicator measurableSet_Iic (fun r => G u (u * r)),
        show (fun r : ℝ => (Iic (0 : ℝ)).indicator (fun r => G u (u * r)) r)
            = ({(0 : ℝ)} : Set ℝ).indicator (fun r => G u (u * r)) from by
          funext r
          by_cases hr : r ∈ Iic (0 : ℝ)
          · rw [Set.indicator_of_mem hr]
            by_cases hr0 : r = 0
            · rw [Set.indicator_of_mem (show r ∈ ({(0 : ℝ)} : Set ℝ) from hr0)]
            · have hneg : u * r < 0 := by
                have hlt : r < 0 := lt_of_le_of_ne (by simpa using hr) hr0
                nlinarith [hlt, hu]
              have hz : G u (u * r) = 0 := by
                rw [show G u (u * r) = A.indicator F (u - u * r, u * r) from rfl]
                by_cases hc : t * (u * r) ≤ (1 - t) * (u - u * r)
                · rw [Set.indicator_of_mem (show (u - u * r, u * r) ∈ A from hc),
                    show F (u - u * r, u * r)
                      = gammaPDF a 1 (u - u * r) * gammaPDF b 1 (u * r) from rfl,
                    gammaPDF_of_neg hneg, mul_zero]
                · rw [Set.indicator_of_notMem (show (u - u * r, u * r) ∉ A from hc)]
              rw [Set.indicator_of_notMem
                (show r ∉ ({(0 : ℝ)} : Set ℝ) from hr0), hz]
          · rw [Set.indicator_of_notMem hr, Set.indicator_of_notMem
              (show r ∉ ({(0 : ℝ)} : Set ℝ) from fun h => hr (le_of_eq (by simpa using h)))],
        lintegral_indicator (measurableSet_singleton 0)]
      exact setLIntegral_of_measure_eq_zero Real.volume_singleton _
    have hHz : ∫⁻ r, G u (u * r) = ∫⁻ r in Ioi (0 : ℝ), K u r := by
      rw [← lintegral_add_compl (fun r : ℝ => G u (u * r)) measurableSet_Ioi,
        hsub, add_zero]
      refine setLIntegral_congr_fun measurableSet_Ioi fun r hr => ?_
      simp only [Set.mem_Ioi] at hr
      by_cases hc : t * (u * r) ≤ (1 - t) * (u - u * r)
      · have hr1 : r ≤ 1 - t := by nlinarith [hc, hu]
        rw [show G u (u * r) = A.indicator F (u - u * r, u * r) from rfl,
          Set.indicator_of_mem (show (u - u * r, u * r) ∈ A from hc)]
        dsimp only [K]
        rw [ite_eq_left ⟨hr, hr1⟩]
      · have hr1 : ¬ (r ≤ 1 - t) := fun h => hc (by nlinarith [h, hu])
        rw [show G u (u * r) = A.indicator F (u - u * r, u * r) from rfl,
          Set.indicator_of_notMem (show (u - u * r, u * r) ∉ A from hc)]
        dsimp only [K]
        rw [ite_eq_right (by rintro ⟨-, h⟩; exact hr1 h)]
    have hcancel : ENNReal.ofReal u * ENNReal.ofReal u⁻¹ = 1 := by
      rw [← ENNReal.ofReal_mul (le_of_lt hu), mul_inv_cancel₀ (ne_of_gt hu),
        ENNReal.ofReal_one]
    rw [hHz] at hlin
    calc ∫⁻ y, G u y
        = (ENNReal.ofReal u * ENNReal.ofReal u⁻¹) * ∫⁻ y, G u y := by
          rw [hcancel, one_mul]
      _ = ENNReal.ofReal u * (ENNReal.ofReal u⁻¹ * ∫⁻ y, G u y) := by rw [mul_assoc]
      _ = ENNReal.ofReal u * ∫⁻ r, K u r := by
        exact congrArg (fun x => ENNReal.ofReal u * x) (hlin.symm.trans (hKfull u))
  have h5 : ∫⁻ u, ∫⁻ y, G u y = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ∫⁻ r, K u r := by
    rw [h5b]
    exact setLIntegral_congr_fun measurableSet_Ioi h5c

  -- ### Step 6/7 : pull the constant in, then Fubini on the `(u, r)`-integral
  have hKm2 : Measurable (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * K p.1 p.2) := by
    apply Measurable.mul
    · exact measurable_fst.ennreal_ofReal
    · dsimp only [K]
      apply Measurable.ite
      · exact (measurableSet_lt measurable_const measurable_snd).inter
          (measurableSet_le measurable_snd measurable_const)
      · exact (((measurable_gammaPDFReal a 1).ennreal_ofReal.comp
            (measurable_fst.sub (measurable_fst.mul measurable_snd))).mul
          ((measurable_gammaPDFReal b 1).ennreal_ofReal.comp
            (measurable_fst.mul measurable_snd)))
      · exact measurable_const
  have h67 : ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ∫⁻ r, K u r
      = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r := by
    rw [show (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * ∫⁻ r, K u r)
        = ∫⁻ u in Ioi (0 : ℝ), ∫⁻ r, ENNReal.ofReal u * K u r from
      setLIntegral_congr_fun measurableSet_Ioi
        (fun u _ => (lintegral_const_mul (ENNReal.ofReal u) (hKr u)).symm)]
    rw [lintegral_lintegral_swap
      (f := fun u r : ℝ => ENNReal.ofReal u * K u r)
      (show AEMeasurable (Function.uncurry (fun u r : ℝ => ENNReal.ofReal u * K u r))
          ((volume.restrict (Ioi (0 : ℝ))).prod volume) from hKm2.aemeasurable)]
    have hKz : ∀ r : ℝ, r ≤ 0 → (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r) = 0 := by
      intro r hr
      rw [show (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
          = ∫⁻ _u in Ioi (0 : ℝ), (0 : ℝ≥0∞) from
        setLIntegral_congr_fun measurableSet_Ioi (fun u _ => by
          dsimp only [K]
          rw [ite_eq_right (by rintro ⟨h, -⟩; exact absurd h (not_lt.mpr hr)), mul_zero])]
      exact lintegral_zero
    have hrestrict : ∫⁻ r, ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r
        = ∫⁻ r in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r := by
      rw [← lintegral_add_compl
        (fun r : ℝ => ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r) measurableSet_Ioi,
        Set.compl_Ioi]
      have hzero : ∫⁻ r in Iic (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r = 0 := by
        rw [show (∫⁻ r in Iic (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
            = ∫⁻ _r in Iic (0 : ℝ), (0 : ℝ≥0∞) from
          setLIntegral_congr_fun measurableSet_Iic (fun r hr => by
            simp only [Set.mem_Iic] at hr
            exact hKz r hr)]
        exact lintegral_zero
      rw [hzero, add_zero]
    exact hrestrict

  -- ### Step 8 : evaluate the inner `u`-integral
  have h8 : ∀ r ∈ Ioi (0 : ℝ), (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
      = (if r ≤ 1 - t then ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
          / (Real.Gamma a * Real.Gamma b)) else 0)
        * ENNReal.ofReal (Real.Gamma (a + b)) := by
    intro r hr
    simp only [Set.mem_Ioi] at hr
    by_cases hr1 : r ≤ 1 - t
    · rw [ite_eq_left hr1]
      have hstep : ∀ u ∈ Ioi (0 : ℝ), ENNReal.ofReal u * K u r
          = ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
              / (Real.Gamma a * Real.Gamma b))
            * ENNReal.ofReal (u ^ (a + b - 1) * Real.exp (-u)) := by
        intro u hu
        simp only [Set.mem_Ioi] at hu
        dsimp only [K]
        rw [ite_eq_left ⟨hr, hr1⟩]
        exact gammaPDF_mul_factor a b r u ha hb hu hr (by linarith)
      rw [show (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
          = ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
              / (Real.Gamma a * Real.Gamma b))
            * ENNReal.ofReal (u ^ (a + b - 1) * Real.exp (-u)) from
        setLIntegral_congr_fun measurableSet_Ioi hstep]
      rw [lintegral_const_mul _ (by fun_prop)]
      rw [lintegral_rpow_exp_neg_Ioi (a + b) (by linarith)]
    · rw [ite_eq_right hr1]
      rw [show (∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
          = ∫⁻ _u in Ioi (0 : ℝ), (0 : ℝ≥0∞) from
        setLIntegral_congr_fun measurableSet_Ioi (fun u _ => by
          dsimp only [K]
          rw [ite_eq_right (by rintro ⟨-, h⟩; exact hr1 h), mul_zero])]
      exact lintegral_zero.trans (zero_mul _).symm

  -- ### Step 9 : assemble, reflect, and match `betaMeasure`
  have h9 : ∫⁻ r in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r
      = ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
        * ∫⁻ w in Icc t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) := by
    rw [show (∫⁻ r in Ioi (0 : ℝ), ∫⁻ u in Ioi (0 : ℝ), ENNReal.ofReal u * K u r)
        = ∫⁻ r in Ioi (0 : ℝ), (if r ≤ 1 - t then ENNReal.ofReal ((1 - r) ^ (a - 1)
            * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b)) else 0)
          * ENNReal.ofReal (Real.Gamma (a + b)) from
      setLIntegral_congr_fun measurableSet_Ioi h8]
    -- `(if p then c else 0) * d = if p then c * d else 0`, then restrict to `Ioc 0 (1-t)`
    rw [show (∫⁻ r in Ioi (0 : ℝ), (if r ≤ 1 - t then ENNReal.ofReal ((1 - r) ^ (a - 1)
            * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b)) else 0)
          * ENNReal.ofReal (Real.Gamma (a + b)))
        = ∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
            / (Real.Gamma a * Real.Gamma b)) * ENNReal.ofReal (Real.Gamma (a + b)) from by
      rw [← lintegral_indicator measurableSet_Ioi, ← lintegral_indicator measurableSet_Ioc]
      refine lintegral_congr fun r => ?_
      by_cases hr : 0 < r
      · by_cases hr1 : r ≤ 1 - t
        · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
            Set.indicator_of_mem (show r ∈ Ioc (0 : ℝ) (1 - t) from ⟨hr, hr1⟩)]
          rw [ite_eq_left hr1]
        · rw [Set.indicator_of_mem (show r ∈ Ioi (0 : ℝ) from hr),
            Set.indicator_of_notMem (show r ∉ Ioc (0 : ℝ) (1 - t) from fun h => hr1 h.2)]
          rw [ite_eq_right hr1, zero_mul]
      · rw [Set.indicator_of_notMem (show r ∉ Ioi (0 : ℝ) from hr),
          Set.indicator_of_notMem (show r ∉ Ioc (0 : ℝ) (1 - t) from fun h => hr h.1)]]
    -- factor out the constant `Γ(a+b)/(Γa Γb)`
    rw [show (∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
            / (Real.Gamma a * Real.Gamma b)) * ENNReal.ofReal (Real.Gamma (a + b)))
        = ENNReal.ofReal (Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b))
          * ∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)) from by
      rw [show (∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)
              / (Real.Gamma a * Real.Gamma b)) * ENNReal.ofReal (Real.Gamma (a + b)))
          = ∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal (Real.Gamma (a + b)
              / (Real.Gamma a * Real.Gamma b))
            * ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)) from by
        refine setLIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
        have hr1 : 0 < r := hr.1
        have hA : 0 ≤ (1 - r) ^ (a - 1) * r ^ (b - 1) :=
          mul_nonneg (Real.rpow_nonneg (by linarith [hr.2, ht0, ht1]) _)
            (Real.rpow_nonneg hr1.le _)
        have hG : 0 ≤ Real.Gamma a * Real.Gamma b :=
          le_of_lt (mul_pos (Real.Gamma_pos_of_pos ha) (Real.Gamma_pos_of_pos hb))
        have hC : 0 ≤ (1 - r) ^ (a - 1) * r ^ (b - 1) / (Real.Gamma a * Real.Gamma b) :=
          div_nonneg hA hG
        have hB : 0 ≤ Real.Gamma (a + b) / (Real.Gamma a * Real.Gamma b) :=
          div_nonneg (Real.Gamma_pos_of_pos (by linarith)).le hG
        rw [← ENNReal.ofReal_mul hC, ← ENNReal.ofReal_mul hB]
        congr 1
        ring]
      rw [lintegral_const_mul _ (by fun_prop)]]
    congr 1
    -- reflection `r ↦ 1 - r`
    rw [show (∫⁻ r in Ioc (0 : ℝ) (1 - t), ENNReal.ofReal ((1 - r) ^ (a - 1) * r ^ (b - 1)))
        = ∫⁻ w in Ico t 1, ENNReal.ofReal ((1 - (1 - w)) ^ (a - 1) * (1 - w) ^ (b - 1)) from
      setLIntegral_one_sub' measurableSet_Ioc (by fun_prop) (by
        ext w
        simp only [Set.mem_preimage, Set.mem_Ioc, Set.mem_Ico]
        constructor <;> intro h <;> constructor <;> linarith)]
    rw [show (∫⁻ w in Ico t 1, ENNReal.ofReal ((1 - (1 - w)) ^ (a - 1) * (1 - w) ^ (b - 1)))
        = ∫⁻ w in Ico t 1, ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)) from by
      refine lintegral_congr fun w => ?_
      rw [show (1 : ℝ) - (1 - w) = w by ring]]
    -- `Ico t 1` vs `Icc t 1`
    exact setLIntegral_congr_of_diff_subset_singleton
      (c := 1)
      (by
        intro x hx
        simp only [Set.mem_sdiff, Set.mem_Ico, Set.mem_Icc] at hx
        exact (hx.2 ⟨hx.1.1, le_of_lt hx.1.2⟩).elim)
      (by
        intro x hx
        simp only [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ico] at hx
        simp only [Set.mem_singleton_iff]
        exact le_antisymm hx.1.2 (not_lt.mp fun h => hx.2 ⟨hx.1.1, h⟩))
      (fun w => ENNReal.ofReal (w ^ (a - 1) * (1 - w) ^ (b - 1)))

  rw [h5, h67, h9]
  rw [← betaMeasure_Ici a b t ha hb ht0 ht1]


end TSDPP

