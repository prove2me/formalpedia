-- Prove2me | solution 1 for lean_workbook_plus_73813
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T03:24:52.880832+00:00
-- url     : https://prove2.me/submissions/c3a9ded3-ea97-4e81-a1bc-7cc80d40abf6

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace Workbook73813

theorem full_source (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1 / a + 1 / b + 9 / c = 3) : 25 / 3 ≤ a + b + c := by
  have hid : (a+b+c)*(1/a+1/b+9/c)-25 =
      (a-b)^2/(a*b)+(3*a-c)^2/(a*c)+(3*b-c)^2/(b*c) := by
    field_simp
    <;> ring
  have hn : 0 ≤ (a-b)^2/(a*b)+(3*a-c)^2/(a*c)+(3*b-c)^2/(b*c) := by
    positivity
  rw [h] at hid
  linarith

theorem source_attainment :
    1 / (5 / 3 : ℝ) + 1 / (5 / 3 : ℝ) + 9 / (5 : ℝ) = 3 ∧
    (5 / 3 : ℝ) + (5 / 3 : ℝ) + 5 = 25 / 3 := by
  norm_num

private theorem product_bound (x y z : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z)
    (h : x+y+z=3) : x*y*z ≤ 1 := by
  have hx4 : 0 ≤ 4-x := by linarith
  have hn : 0 ≤ (4-x)*(x-1)^2+x*(y-z)^2 := by positivity
  have he : z=3-x-y := by linarith
  have hid : 4-4*x*y*z=(4-x)*(x-1)^2+x*(y-z)^2 := by
    rw [he]
    ring
  linarith

-- Also valid under just the genuine source hypotheses.
theorem source_product_lower (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : 1/a+1/b+9/c=3) : 9 ≤ a*b*c := by
  have hh := product_bound (1/a) (1/b) (9/c) (by positivity) (by positivity)
    (by positivity) h
  have he : (1/a)*(1/b)*(9/c) = 9/(a*b*c) := by ring
  rw [he] at hh
  have hmul := (div_le_iff₀ (by positivity : 0 < a*b*c)).mp hh
  linarith

end Workbook73813

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (habc : a * b * c = 1) (h : 1 / a + 1 / b + 9 / c = 3) :
    a + b + c >= 25 / 3 ∧ (a = 5 / 3 ∧ b = 5 / 3 ∧ c = 5) := by
  have hp := Workbook73813.source_product_lower a b c ha hb hc h
  exfalso
  linarith
