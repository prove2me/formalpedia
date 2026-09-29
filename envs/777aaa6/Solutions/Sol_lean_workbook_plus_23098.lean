-- Prove2me | solution 1 for lean_workbook_plus_23098
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T22:39:39.590074+00:00
-- url     : https://prove2.me/submissions/8b84ecd8-828f-4dc1-9670-36544f6051a1

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x : ℝ) (hx : -1 ≤ x ∧ x ≤ 1) :
  x^8 - x^7 + x^2 - x ≥ -4 := by
  have ha : |x| ≤ 1 := abs_le.mpr hx
  have hp : |x^7| ≤ 1 := by
    simpa only [abs_pow] using (pow_le_one₀ (abs_nonneg x) ha : |x|^7 ≤ 1)
  have h7 : x^7 ≤ 1 := (le_abs_self (x^7)).trans hp
  have h8 : 0 ≤ x^8 := by positivity
  linarith [sq_nonneg x, hx.2]
