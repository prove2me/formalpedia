-- Prove2me | solution 1 for lean_workbook_plus_128
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-05T19:37:54.864086+00:00
-- url     : https://prove2.me/submissions/abc57034-9aa7-4432-b2e5-464357b91812

import Mathlib.Tactic
import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false
set_option maxRecDepth 2048
set_option maxHeartbeats 300000



theorem solution : ∀ n:ℕ, 6 * 4 ^ n ≡ 6 [ZMOD 9] := by
  intro n
  induction n with
  | zero => norm_num [Int.ModEq]
  | succ n ih =>
    calc
      (6:ℤ)*4^(n+1) = 4*(6*4^n) := by ring
      _ ≡ 4*6 [ZMOD 9] := ih.mul_left 4
      _ ≡ 6 [ZMOD 9] := by decide
