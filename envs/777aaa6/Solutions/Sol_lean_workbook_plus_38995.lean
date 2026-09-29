-- Prove2me | solution 1 for lean_workbook_plus_38995
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:38:40.075286+00:00
-- url     : https://prove2.me/submissions/c08059bc-86ee-418c-92ec-02c2631e6148

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) (h : 19 ∣ 3 * x + 7 * y) : 19 ∣ 43 * x + 75 * y := by
  (intros; omega)
