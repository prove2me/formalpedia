-- Prove2me | solution 1 for lean_workbook_plus_27735
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:40:39.115414+00:00
-- url     : https://prove2.me/submissions/25f9cfff-020a-429c-910e-b68c21237a47

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℤ) : a + 210 - b + 10 - c + 107 = a - b - c + 327 := by
  (intros; omega)
