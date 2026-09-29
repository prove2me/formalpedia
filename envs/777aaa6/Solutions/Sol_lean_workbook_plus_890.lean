-- Prove2me | solution 1 for lean_workbook_plus_890
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:59:05.104611+00:00
-- url     : https://prove2.me/submissions/9cd6942a-91b9-4ce9-8bfb-5457c0149391

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ n : ℕ, Odd (9^(n-1) + 3^(n-1) + 1) := by
  intro n
  intros
  grind
