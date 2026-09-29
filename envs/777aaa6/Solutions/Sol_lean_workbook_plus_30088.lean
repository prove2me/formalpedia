-- Prove2me | solution 1 for lean_workbook_plus_30088
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:28:05.918745+00:00
-- url     : https://prove2.me/submissions/999c2b73-ec68-4559-bb12-8d97ce0164d0

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution : ∀ n m : ℤ, Odd n ∧ Odd m → Even (n - m) := by
  intro n m
  intros
  grind
