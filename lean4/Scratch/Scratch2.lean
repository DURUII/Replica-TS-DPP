/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal
open Set

namespace TSDPP

example {a b t : ℝ} (ha : 0 < a) (hb : 0 < b) (ht0 : 0 < t) (ht1 : t < 1) :
    (gammaMeasure a 1).prod (gammaMeasure b 1) {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}
      = betaMeasure a b (Ici t) := by
  have hA : MeasurableSet {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1} :=
    measurableSet_le (measurable_const.mul measurable_snd) (measurable_const.mul measurable_fst)
  have hga : Measurable (gammaPDF a 1) := (measurable_gammaPDFReal a 1).ennreal_ofReal
  have hgb : Measurable (gammaPDF b 1) := (measurable_gammaPDFReal b 1).ennreal_ofReal
  simp only [gammaMeasure]
  rw [MeasureTheory.prod_withDensity hga hgb, withDensity_apply _ hA]
  show ∫⁻ a_1 in {p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1},
      gammaPDF a 1 a_1.1 * gammaPDF b 1 a_1.2 ∂(volume.prod volume) = betaMeasure a b (Ici t)
  rw [← lintegral_indicator hA (fun p : ℝ × ℝ => gammaPDF a 1 p.1 * gammaPDF b 1 p.2)]
  rw [lintegral_prod_symm _ (by
    exact ((measurable_gammaPDFReal a 1).ennreal_ofReal.comp measurable_fst |>.mul
      ((measurable_gammaPDFReal b 1).ennreal_ofReal.comp measurable_snd) |>.indicator hA).aemeasurable)]
  show ∫⁻ y, ∫⁻ x, ({p : ℝ × ℝ | t * p.2 ≤ (1 - t) * p.1}.indicator
      (fun p : ℝ × ℝ => gammaPDF a 1 p.1 * gammaPDF b 1 p.2) (x, y)) ∂volume ∂volume
      = betaMeasure a b (Ici t)
  sorry

end TSDPP
