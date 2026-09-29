-- Prove2me | solution 1 for lean_workbook_plus_43932
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:32:02.008317+00:00
-- url     : https://prove2.me/submissions/1f61d82e-76f1-47da-8a61-27006a4b2b6f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution :  ∀ a : ℝ, a >= 3 → (a^2 - 2 * a + 4) / a ≥ 2 + a^2 / (3 * (6 + a)) := by
  intro a
  intros
  field_simp at * <;> nlinarith [sq_nonneg a]
