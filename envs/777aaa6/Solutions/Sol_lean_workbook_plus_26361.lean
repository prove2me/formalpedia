-- Prove2me | solution 1 for lean_workbook_plus_26361
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T22:40:31.266935+00:00
-- url     : https://prove2.me/submissions/2b1cbc01-c878-475e-a111-6fdde451ffc6

import Mathlib.Analysis.Complex.Basic

theorem solution (a b c x y z : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) (hz : 0 < z) : (a^3 / x + b^3 / y + c^3 / z) ≥ (a^3 + b^3 + c^3) / (3 * (x + y + z)) := by
  have hs : 0 < 3 * (x + y + z) := by positivity
  have h1 : a ^ 3 / (3 * (x + y + z)) ≤ a ^ 3 / x :=
    div_le_div_of_nonneg_left (by positivity) hx (by linarith)
  have h2 : b ^ 3 / (3 * (x + y + z)) ≤ b ^ 3 / y :=
    div_le_div_of_nonneg_left (by positivity) hy (by linarith)
  have h3 : c ^ 3 / (3 * (x + y + z)) ≤ c ^ 3 / z :=
    div_le_div_of_nonneg_left (by positivity) hz (by linarith)
  have hsum : (a ^ 3 + b ^ 3 + c ^ 3) / (3 * (x + y + z))
      = a ^ 3 / (3 * (x + y + z)) + b ^ 3 / (3 * (x + y + z)) + c ^ 3 / (3 * (x + y + z)) := by
    rw [add_div, add_div]
  rw [ge_iff_le, hsum]
  linarith
