/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

#check @MeasureTheory.prod_withDensity
#check @lintegral_zero_measure
#check @Measure.zero_apply
#check @volume_singleton
#check @Real.volume_singleton
#check @Measure.restrict_singleton
#check @Measure.restrict_eq_zero
#check @ae_eq_set
#check @measure_mono
#check @Measure.restrict_apply
#check @MeasurableSet.singleton
#check @measurableSet_singleton
#check @Set.EqOn
#check @MeasureTheory.Measure.prod_apply
#check @Measure.prod_apply_symm
#check @integral_eq_lintegral_of_nonneg_ae
#check @intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
#check @Real.Gamma_pos_of_pos
#check @Real.Gamma_ne_zero_of_pos
#check @ProbabilityTheory.beta_pos
#check @ProbabilityTheory.beta
#check @ProbabilityTheory.betaPDF_of_pos_lt_one
#check @ProbabilityTheory.betaPDF_eq_zero_of_one_le
#check @ProbabilityTheory.betaPDF_eq_zero_of_nonpos
#check @ProbabilityTheory.betaPDF_eq
#check @ProbabilityTheory.betaMeasure
#check @MeasureTheory.Measure.restrict_restrict
#check @Measure.restrict_union
#check @lintegral_union
#check @lintegral_union_ae
