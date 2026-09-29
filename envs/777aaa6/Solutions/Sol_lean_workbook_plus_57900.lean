-- Prove2me | solution 1 for lean_workbook_plus_57900
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T20:51:59.018429+00:00
-- url     : https://prove2.me/submissions/8f286edd-3812-42e5-87a4-ecb500497e54

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecificLimits.Normed

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 30000



theorem solution (a : ℝ) (h : a = 1 / 2) : ∑' i : ℕ, a ^ i = 2 := by
  rw [h, tsum_geometric_two]
