/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import TSDPP.BetaGammaChernoff
open MeasureTheory ProbabilityTheory
namespace TSDPP
example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β)
    (hmap : betaMeasure α β = ((gammaMeasure α 1).prod (gammaMeasure β 1)).map
              (fun p : ℝ × ℝ => p.1 / (p.1 + p.2))) :
    IsProbabilityMeasure (betaMeasure α β) := by
  have hgα : IsProbabilityMeasure (gammaMeasure α 1) := isProbabilityMeasure_gammaMeasure hα one_pos
  have hgβ : IsProbabilityMeasure (gammaMeasure β 1) := isProbabilityMeasure_gammaMeasure hβ one_pos
  rw [hmap]
  infer_instance
example {α β : ℝ} (hα : 0 < α) (hβ : 0 < β) :
    IsProbabilityMeasure ((betaMeasure α β).prod (betaMeasure α β)) := by
  have := isProbabilityMeasureBeta hα hβ
  infer_instance
end TSDPP
