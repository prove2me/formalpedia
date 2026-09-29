-- Prove2me | solution 1 for lean_workbook_plus_18761
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-06T02:26:41.995618+00:00
-- url     : https://prove2.me/submissions/693d98bb-6db3-4efc-8ea4-60ad941a89f3

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false

private theorem workbook_source_18761 (a b c : ℝ)
    (h : a^2*b+b^2*c+c^2*a+a*b^2+b*c^2+c*a^2=4+2*a*b*c) :
    (a^2+b^2)*(b^2+c^2)*(c^2+a^2) ≥ 8 := by
  have hsq : 0 ≤ (a-b)^2*(a-c)^2*(b-c)^2 := by positivity
  have hid : 2*((a^2+b^2)*(b^2+c^2)*(c^2+a^2)) -
      (a^2*b+b^2*c+c^2*a+a*b^2+b*c^2+c*a^2-2*a*b*c)^2 =
      (a-b)^2*(a-c)^2*(b-c)^2 := by ring
  have ht : a^2*b+b^2*c+c^2*a+a*b^2+b*c^2+c*a^2-2*a*b*c = 4 := by linarith
  rw [ht] at hid
  nlinarith

theorem solution (a b c : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (habc : a * b * c = 1) (h : a^2 * b + b^2 * c + c^2 * a + a * b^2 + b * c^2 + c * a^2 = 4 + 2 * a * b * c) : (a^2 + b^2) * (b^2 + c^2) * (c^2 + a^2) ≥ 8   := by
  exact workbook_source_18761 a b c h
