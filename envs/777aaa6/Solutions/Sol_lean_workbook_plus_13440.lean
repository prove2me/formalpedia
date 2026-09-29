-- Prove2me | solution 1 for lean_workbook_plus_13440
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:19:32.433151+00:00
-- url     : https://prove2.me/submissions/fbdd2272-029d-4ed7-ab76-c1b5e625b845

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 0 < 6) : (Nat.choose 6 1 * 2 ^ 1 + Nat.choose 6 2 * 2 ^ 2 + Nat.choose 6 3 * 2 ^ 3 + Nat.choose 6 4 * 2 ^ 4 + Nat.choose 6 5 * 2 ^ 5 + Nat.choose 6 6 * 2 ^ 6) = 728 := by
  decide
