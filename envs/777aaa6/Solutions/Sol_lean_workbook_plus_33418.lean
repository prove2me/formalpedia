-- Prove2me | solution 1 for lean_workbook_plus_33418
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:25.635612+00:00
-- url     : https://prove2.me/submissions/ba478c5a-8055-463d-bd28-0cb9d730a282

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 3 ≤ 10) (h₂ : 2 ≤ 5) : (Nat.choose 10 3) * (Nat.choose 5 2) = 1200 := by
  decide
