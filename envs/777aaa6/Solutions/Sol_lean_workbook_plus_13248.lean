-- Prove2me | solution 1 for lean_workbook_plus_13248
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:46:06.438793+00:00
-- url     : https://prove2.me/submissions/8719c613-4af3-41f1-8881-c330512d0eb3

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 100000



theorem solution (A0 A1 A2 : ℝ) (hA : ∀ x : ℝ, -1 ≤ x ∧ x ≤ 1 → -1 ≤ A0 + A1 * x + A2 * x ^ 2 ∧ A0 + A1 * x + A2 * x ^ 2 ≤ 2) : -3 ≤ A2 ∧ A2 ≤ 3 := by
  have h0 := hA 0 (by norm_num)
  have hp := hA 1 (by norm_num)
  have hm := hA (-1) (by norm_num)
  clear hA
  constructor
  · linear_combination (1/2)*hp.1 + (1/2)*hm.1 + h0.2
  · linear_combination h0.1 + (1/2)*hp.2 + (1/2)*hm.2
