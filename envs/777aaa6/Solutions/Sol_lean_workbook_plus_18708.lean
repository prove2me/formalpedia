-- Prove2me | solution 1 for lean_workbook_plus_18708
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:39:21.022227+00:00
-- url     : https://prove2.me/submissions/635471c4-c1c9-496b-b917-8ff50fc4c8ef

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ n : ℕ, (Nat.floor (n / 3) + Nat.floor ((n + 2) / 6) + Nat.floor ((n + 4) / 6) = Nat.floor (n / 2) + Nat.floor ((n + 3) / 6)) := by
  intro n
  intros
  norm_num at * <;> first | omega | nlinarith | grind
