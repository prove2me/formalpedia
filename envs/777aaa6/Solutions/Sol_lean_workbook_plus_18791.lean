-- Prove2me | solution 1 for lean_workbook_plus_18791
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:58:33.084627+00:00
-- url     : https://prove2.me/submissions/4a435fd9-69d1-42e2-8a75-d430869a6f3f

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ n : ℕ, 17^(2 * n + 1) ≡ (-8)^(2 * n + 1) [ZMOD 25] := by
  intro n
  intros
  exact?
