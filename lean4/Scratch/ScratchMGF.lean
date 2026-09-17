import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace TSDPP

theorem measurable_gammaPDF (a r : ℝ) : Measurable (gammaPDF a r) :=
  (measurable_gammaPDFReal a r).ennreal_ofReal

example {a : ℝ} (ha : 0 < a) {t : ℝ} (ht : t < 1) :
    ∫ x, gammaPDFReal a 1 x * Real.exp (t * x) = (1 - t) ^ (-a) := by
  have hpt : Set.EqOn (fun x : ℝ => gammaPDFReal a 1 x * Real.exp (t * x))
      (fun x : ℝ => 1 ^ a / Real.Gamma a * (x ^ (a - 1) * Real.exp (-((1 - t) * x))))
      (Set.Ioi 0) := by
    intro x hx
    have hx' : (0 : ℝ) < x := hx
    simp only [gammaPDFReal, ite_eq_left hx'.le]
    rw [show -((1 - t) * x) = -(1 * x) + t * x by ring, Real.exp_add]
    ring
  have hsupp : ∫ x, gammaPDFReal a 1 x * Real.exp (t * x)
      = ∫ x in Set.Ici 0, gammaPDFReal a 1 x * Real.exp (t * x) := by
    have hzero : ∀ x, x ∉ Set.Ici 0 → gammaPDFReal a 1 x * Real.exp (t * x) = 0 := by
      intro x hx
      simp only [Set.mem_Ici, not_le] at hx
      rw [gammaPDFReal, ite_eq_right (not_le.mpr hx), zero_mul]
    rw [setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
  rw [hsupp, integral_Ici_eq_integral_Ioi,
    setIntegral_congr_fun measurableSet_Ioi hpt, integral_const_mul,
    Real.integral_rpow_mul_exp_neg_mul_Ioi ha (by linarith : (0 : ℝ) < 1 - t)]
  rw [Real.one_rpow]
  have hG : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  rw [mul_comm ((1 / (1 - t)) ^ a) (Real.Gamma a), ← mul_assoc, one_div,
    inv_mul_cancel₀ hG, one_mul]
  rw [one_div, Real.inv_rpow (by linarith : (0 : ℝ) ≤ 1 - t),
    Real.rpow_neg (by linarith : (0 : ℝ) ≤ 1 - t)]

end TSDPP
