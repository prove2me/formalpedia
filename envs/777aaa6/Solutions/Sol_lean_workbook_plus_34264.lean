-- Prove2me | solution 1 for lean_workbook_plus_34264
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:22:06.01097+00:00
-- url     : https://prove2.me/submissions/76b8a2c9-363a-4dc5-bb8b-95b7adb4dbd6

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n k : ℕ) : n = (2 * k ^ 2) ^ 2 + (2 * k) ^ 2 → n + 1 = (2 * k ^ 2 + 1) ^ 2 + 0 ^ 2 ∧ n + 2 = (2 * k ^ 2 + 1) ^ 2 + 1 ^ 2 := by
  intros
  grind
