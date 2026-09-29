-- Prove2me | solution 1 for lean_workbook_plus_61758
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:53:38.305555+00:00
-- url     : https://prove2.me/submissions/fc5899ba-2102-4824-8aac-6d193abef1ab

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {a b : ℤ} (hab : a * b = 1) (n : ℕ) : a ^ n * b ^ n = 1 := by
  intros
  exact?
