-- Prove2me | solution 1 for lean_workbook_plus_22669
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:59:48.148837+00:00
-- url     : https://prove2.me/submissions/9d1435d4-231c-4ade-8e8f-089ea3af4217

import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 200000



theorem solution (x y z : ℝ) (h1 : 1 - x*y ≥ 0) (h2 : 1 - x*z ≥ 0) (h3 : 1 - y*z ≥ 0) : (1 - x*y) * (1 - y*z) * (1 - z*x) ≥ 0 := by
  have h4 : 0 ≤ 1-z*x := by nlinarith
  exact mul_nonneg (mul_nonneg h1 h3) h4
