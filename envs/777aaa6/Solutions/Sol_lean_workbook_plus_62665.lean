-- Prove2me | solution 1 for lean_workbook_plus_62665
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T18:00:09.63723+00:00
-- url     : https://prove2.me/submissions/8600a914-c214-49be-8a1e-a8577d5d8b29

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n : ℕ) (k : ℕ) (hn : 2 ≤ n) : n - 1 ∣ n^k - 1 := by
  intros
  exact?
