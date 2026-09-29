-- Prove2me | solution 1 for lean_workbook_plus_26926
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:52:22.525356+00:00
-- url     : https://prove2.me/submissions/f7ecd6f4-c4bc-4a47-992e-e5563b786be1

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution {p m n : ℕ} (hp : p.Prime) (h : m ∣ n) : p^m - 1 ∣ p^n - 1 := by
  intros
  exact?
