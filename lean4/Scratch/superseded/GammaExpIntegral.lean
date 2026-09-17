import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

/-- The Gamma integral in `ℝ≥0∞` form: for `0 < a`,
`∫⁻ u in (0,∞), ofReal (u^(a-1) * exp(-u)) = ofReal (Γ a)`. -/
theorem lintegral_rpow_exp_neg_Ioi (a : ℝ) (ha : 0 < a) :
    ∫⁻ u in Set.Ioi (0:ℝ), ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u))
      = ENNReal.ofReal (Real.Gamma a) := by
  -- Step 1: the Bochner integral evaluates to `Γ a`.
  have hInt : ∫ u in Set.Ioi (0:ℝ), u ^ (a - 1) * Real.exp (-u) = Real.Gamma a := by
    simpa only [one_mul, one_div_one, Real.one_rpow] using
      Real.integral_rpow_mul_exp_neg_mul_Ioi (a := a) (r := 1) ha one_pos
  -- Step 2: nonnegativity of the integrand on `Ioi 0`.
  have hnonneg : 0 ≤ᵐ[volume.restrict (Set.Ioi (0:ℝ))]
      fun u : ℝ => u ^ (a - 1) * Real.exp (-u) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    exact mul_nonneg (Real.rpow_nonneg hu.le _) (Real.exp_nonneg _)
  -- Step 3: strong measurability of the integrand.
  have hcont : AEStronglyMeasurable (fun u : ℝ => u ^ (a - 1) * Real.exp (-u))
      (volume.restrict (Set.Ioi (0:ℝ))) := by fun_prop
  -- Step 4: convert the Bochner integral to a `lintegral`.
  have h := integral_eq_lintegral_of_nonneg_ae hnonneg hcont
  rw [hInt] at h
  -- Step 5: the `lintegral` is finite.
  have htop : (∫⁻ u, ENNReal.ofReal (u ^ (a - 1) * Real.exp (-u))
      ∂(volume.restrict (Set.Ioi (0:ℝ)))) ≠ ⊤ := by
    intro hT
    rw [hT, ENNReal.toReal_top] at h
    exact (Real.Gamma_pos_of_pos ha).ne' h
  -- Step 6: conclude by identifying both sides.
  rw [← ENNReal.ofReal_toReal htop, h.symm]

end TSDPP
