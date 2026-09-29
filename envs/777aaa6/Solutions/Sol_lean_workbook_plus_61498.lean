-- Prove2me | solution 1 for lean_workbook_plus_61498
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:54.088471+00:00
-- url     : https://prove2.me/submissions/5865fa73-46a1-4015-8e2e-89d93c8ffcec

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 14 * 3 + 2 * 5 = 52) : 14 * 3 + 2 * 5 = 52 := by
  norm_num
