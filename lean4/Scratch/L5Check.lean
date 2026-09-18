import Mathlib
import TSDPP.BetaConcentration

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

#check @measureReal_def
#check @measure_ne_top
#check @MeasureTheory.Measure.ofReal_real
#check @MeasureTheory.Measure.real_apply
#check @MeasureTheory.measureReal_mono
#check @MeasureTheory.Measure.measure_univ
#check @MeasureTheory.Measure.real_le_real
#check @ENNReal.toReal_ofReal
#check @MeasureTheory.Measure.prod_swap
#check @Filter.Eventually.of_forall
#check @Integrable.const_mul
#check @Integrable.mul_const

variable {α β : ℝ}

example (hα : 0 < α) (hβ : 0 < β) : (betaMeasure α β) (Set.univ) = 1 := by
  haveI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  exact measure_univ

example (hα : 0 < α) (hβ : 0 < β) (S : Set ℝ) : (betaMeasure α β).real S ≤ 1 := by
  haveI : IsProbabilityMeasure (betaMeasure α β) := isProbabilityMeasureBeta hα hβ
  rw [measureReal_def]
  exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using measure_mono (Set.subset_univ S))

end TSDPP
