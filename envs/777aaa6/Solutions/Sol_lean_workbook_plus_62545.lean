-- Prove2me | solution 1 for lean_workbook_plus_62545
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T16:46:50.571946+00:00
-- url     : https://prove2.me/submissions/eaa31d86-3c4c-4d7d-a25d-304fc6ba86c9

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (n m a b : ℤ) (h₁ : n > 0 ∧ m > 0) (hab : a ≡ b [ZMOD m]) : n * a ≡ n * b [ZMOD n * m] := by
  intros
  exact Int.ModEq.mul_left' hab
