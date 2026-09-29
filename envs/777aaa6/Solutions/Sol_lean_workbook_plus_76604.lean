-- Prove2me | solution 1 for lean_workbook_plus_76604
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:16:12.863811+00:00
-- url     : https://prove2.me/submissions/29cbbbef-c84f-40ae-991c-3ad715ebddeb

import Mathlib

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h1 : a > b ∧ b > c ∧ c > 2) : (max (2 * a) (3 / b)) + (max (3 * a) (3 / (2 * c))) + (max ((3 * c) / 2) (2 / a)) > 10 := by
  have hA := le_max_left (2*a) (3/b)
  have hB := le_max_left (3*a) (3/(2*c))
  have hC := le_max_left (3*c/2) (2/a)
  rcases h1 with ⟨hab,hbc,hc⟩
  linarith
