-- Prove2me | solution 1 for lean_workbook_plus_60906
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:10:24.211906+00:00
-- url     : https://prove2.me/submissions/ad984c4b-ca33-4e78-8351-1f386584f7ed

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ a : ℝ, 0 ≤ a ∧ a ≤ 2 → 0 ≤ (-2 * a + 4) / (a ^ 2 + 1) := by
  intro a
  intros
  field_simp at * <;> nlinarith [sq_nonneg a]
