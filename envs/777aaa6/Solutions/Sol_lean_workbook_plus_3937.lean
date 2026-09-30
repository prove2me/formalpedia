-- Prove2me | solution 1 for lean_workbook_plus_3937
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-05T19:26:58.584698+00:00
-- url     : https://prove2.me/submissions/f16a86b5-2b91-49fb-8df0-c93757cf676f

import Mathlib.Analysis.Complex.Basic

theorem solution (x y z : ℝ) (hx: x < y) (hy: y < z) : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 > 0 := by
  have h1 : 0 < y - x := sub_pos.mpr hx
  have h2 : 0 < z - y := sub_pos.mpr hy
  have h3 : 0 < z - x := by linarith
  have key : (x - y) ^ 3 + (y - z) ^ 3 + (z - x) ^ 3 = 3 * ((y - x) * (z - y) * (z - x)) := by ring
  rw [key]
  positivity
