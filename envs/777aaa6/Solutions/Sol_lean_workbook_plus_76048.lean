-- Prove2me | solution 1 for lean_workbook_plus_76048
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:52:45.951806+00:00
-- url     : https://prove2.me/submissions/6b0fc01a-3159-4fb5-b163-14a70996e801

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 1 ≤ 20 ∧ 1 ≤ 9) (h₂ : 2 ≤ 20 ∧ 2 ≤ 55) (h₃ : 3 ≤ 20 ∧ 3 ≤ 50) : 9 * (Nat.choose 20 1) + 55 * (Nat.choose 20 2) + 50 * (Nat.choose 20 3) = 67630 := by
  decide
