-- Prove2me | solution 1 for lean_workbook_plus_15426
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:38:24.804457+00:00
-- url     : https://prove2.me/submissions/31119676-b948-45bc-833c-3d8f85ba7f34

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c ≥ 0) (h2 : a + c ≥ 2 * b) (h3 : a ≤ 2 * c) : 2 * (a + b + c) ^ 3 + 27 * a * b * c ≥ 9 * (a * b + b * c + c * a) * (a + b + c) := by
  have h1p : 0 ≤ 2*a-b-c := by linarith [h1.1,h1.2.1]
  have h2p : 0 ≤ a+c-2*b := by linarith
  have h3p : 0 ≤ a+b-2*c := by linarith [h1.1,h1.2.1]
  have hp := mul_nonneg (mul_nonneg h1p h2p) h3p
  nlinarith only [hp]
