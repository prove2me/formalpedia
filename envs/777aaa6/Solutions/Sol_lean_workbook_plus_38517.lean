-- Prove2me | solution 1 for lean_workbook_plus_38517
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:16:59.615503+00:00
-- url     : https://prove2.me/submissions/22900960-c7bf-46bd-a002-e99602fe68b9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 0 < 10) : (Nat.choose 10 1 + Nat.choose 10 3 + Nat.choose 10 5 + Nat.choose 10 7 + Nat.choose 10 9) = 512 := by
  decide
