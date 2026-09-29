-- Prove2me | solution 1 for lean_workbook_plus_20262
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:14:50.607095+00:00
-- url     : https://prove2.me/submissions/01fda4bc-edcb-4f0c-832d-b916cbe8e546

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (hn : 1 < n) : (n + 1) ^ 2 < n ^ 2 + 3 * n ∧ n ^ 2 + 3 * n < (n + 2) ^ 2 := by
  intros
  grind
