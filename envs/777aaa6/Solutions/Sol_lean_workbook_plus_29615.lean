-- Prove2me | solution 1 for lean_workbook_plus_29615
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T08:46:28.663201+00:00
-- url     : https://prove2.me/submissions/554bb832-0057-413c-a19b-bd4d6845a894

import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

open MeasureTheory Set

theorem two_pole_partial_fraction (a b x : ℝ) (hab : a ≠ b) (hxa : x ≠ a) (hxb : x ≠ b) :
    1 / ((x - a) * (x - b)) = 1 / (a - b) * (1 / (x - a) - 1 / (x - b)) := by
  have hab' := sub_ne_zero.mpr hab
  have hxa' := sub_ne_zero.mpr hxa
  have hxb' := sub_ne_zero.mpr hxb
  field_simp
  ring

noncomputable def twoPolePrimitive (a b x : ℝ) : ℝ :=
  (Real.log (x - a) - Real.log (x - b)) / (a - b)

theorem two_pole_primitive_hasDerivAt (a b x : ℝ) (hab : a ≠ b)
    (hxa : x ≠ a) (hxb : x ≠ b) :
    HasDerivAt (twoPolePrimitive a b) (1 / ((x - a) * (x - b))) x := by
  have ha := ((hasDerivAt_id x).sub_const a).log (sub_ne_zero.mpr hxa)
  have hb := ((hasDerivAt_id x).sub_const b).log (sub_ne_zero.mpr hxb)
  have hd := (ha.sub hb).div_const (a - b)
  simp only [id_eq] at hd
  convert hd using 1
  rw [two_pole_partial_fraction a b x hab hxa hxb]
  ring

theorem two_pole_intervalIntegrable (a b l r : ℝ)
    (hpoles : ∀ x ∈ uIcc l r, x ≠ a ∧ x ≠ b) :
    IntervalIntegrable (fun x => 1 / ((x - a) * (x - b))) volume l r := by
  have hc : ContinuousOn (fun x => 1 / ((x - a) * (x - b))) (uIcc l r) :=
    continuousOn_const.div (((continuous_id.sub continuous_const).mul
      (continuous_id.sub continuous_const)).continuousOn)
      (fun x hx => mul_ne_zero (sub_ne_zero.mpr (hpoles x hx).1)
        (sub_ne_zero.mpr (hpoles x hx).2))
  exact hc.intervalIntegrable

theorem two_pole_integral (a b l r : ℝ) (hab : a ≠ b)
    (hpoles : ∀ x ∈ uIcc l r, x ≠ a ∧ x ≠ b) :
    (∫ x in l..r, 1 / ((x - a) * (x - b))) =
      twoPolePrimitive a b r - twoPolePrimitive a b l := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x hx => two_pole_primitive_hasDerivAt a b x hab (hpoles x hx).1 (hpoles x hx).2)
    (two_pole_intervalIntegrable a b l r hpoles)

theorem two_pole_primitive_abs (a b x : ℝ) :
    twoPolePrimitive a b x = (Real.log |x - a| - Real.log |x - b|) / (a - b) := by
  simp only [twoPolePrimitive, Real.log_abs]

theorem quadratic_two_poles_factor (x : ℝ) : x ^ 2 + x - 6 = (x - 2) * (x + 3) := by ring

theorem quadratic_two_poles_nonzero (x : ℝ) (hx : x ^ 2 + x - 6 ≠ 0) :
    x ≠ 2 ∧ x ≠ -3 := by
  constructor <;> intro h <;> subst x <;> norm_num at hx

theorem quadratic_two_poles_antiderivative (x : ℝ) (hx : x ^ 2 + x - 6 ≠ 0) :
    HasDerivAt (fun y => (Real.log (y - 2) - Real.log (y + 3)) / 5)
      (1 / (x ^ 2 + x - 6)) x := by
  have hp := quadratic_two_poles_nonzero x hx
  have h := two_pole_primitive_hasDerivAt 2 (-3) x (by norm_num) hp.1 hp.2
  unfold twoPolePrimitive at h
  norm_num only [twoPolePrimitive, sub_neg_eq_add, show (2 : ℝ) + 3 = 5 by ring] at h
  simpa only [quadratic_two_poles_factor] using h

theorem quadratic_two_poles_integral (l r : ℝ)
    (h : ∀ x ∈ uIcc l r, x ^ 2 + x - 6 ≠ 0) :
    (∫ x in l..r, 1 / (x ^ 2 + x - 6)) =
      (Real.log (r - 2) - Real.log (r + 3)) / 5 -
        (Real.log (l - 2) - Real.log (l + 3)) / 5 := by
  have hi := two_pole_integral 2 (-3) l r (by norm_num)
    (fun x hx => quadratic_two_poles_nonzero x (h x hx))
  norm_num only [twoPolePrimitive, sub_neg_eq_add, show (2 : ℝ) + 3 = 5 by ring] at hi
  simpa only [quadratic_two_poles_factor] using hi

theorem solution : ∀ x : ℝ, x^2 + x - 6 ≠ 0 →
    1 / (x^2 + x - 6) = 1/5 * (1/(x - 2) - 1/(x + 3)) := by
  intro x hx
  have hp := quadratic_two_poles_nonzero x hx
  have h := two_pole_partial_fraction 2 (-3) x (by norm_num) hp.1 hp.2
  norm_num only [sub_neg_eq_add, show (2 : ℝ) + 3 = 5 by ring] at h
  simpa only [quadratic_two_poles_factor] using h

#print axioms two_pole_partial_fraction
#print axioms twoPolePrimitive
#print axioms two_pole_primitive_hasDerivAt
#print axioms two_pole_intervalIntegrable
#print axioms two_pole_integral
#print axioms two_pole_primitive_abs
#print axioms quadratic_two_poles_factor
#print axioms quadratic_two_poles_nonzero
#print axioms quadratic_two_poles_antiderivative
#print axioms quadratic_two_poles_integral
#print axioms solution
