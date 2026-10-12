/-
Copyright (c) 2026 TSDPP contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal
example (f g : ℝ → ℝ≥0∞) : Measure.prod (volume.withDensity f) (volume.withDensity g) = (volume.prod volume).withDensity (fun p : ℝ × ℝ => f p.1 * g p.2) := by
  sorry
#check @Measure.prod_withDensity
#check @Measure.prod_apply_restrict
#check @Measure.map_prod_map_prod
#check @Measure.map_prod_prod
#check @Measure.prod_map_prod
#check @Measure.prod_eq_prod
#check @Measure.ext_of_prod
