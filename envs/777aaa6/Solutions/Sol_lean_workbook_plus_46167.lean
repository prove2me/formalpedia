-- Prove2me | solution 1 for lean_workbook_plus_46167
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:04:50.397562+00:00
-- url     : https://prove2.me/submissions/543fe973-6909-4c35-8c5a-d6ff11b47b74

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h : 5 > 3) : (Nat.choose 5 2 - Nat.choose 3 2) / Nat.choose 5 2 = 7 / 10 := by
  decide
