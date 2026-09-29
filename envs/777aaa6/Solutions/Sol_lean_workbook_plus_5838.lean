-- Prove2me | solution 1 for lean_workbook_plus_5838
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T17:12:08.573811+00:00
-- url     : https://prove2.me/submissions/755028ff-39f0-4e45-b4af-78a6f12f1226

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 50000



theorem solution (a b m : ℤ) (n : ℕ) (h₁ : a ≡ b [ZMOD m]) : a ^ n ≡ b ^ n [ZMOD m] := by
  intros
  exact Int.ModEq.pow n h₁
