-- Prove2me | solution 1 for lean_workbook_plus_6161
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:50:42.04985+00:00
-- url     : https://prove2.me/submissions/518b120f-a046-4e18-a633-e96dd053a1d1

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℤ) : x * (x - y ^ 2) = y ^ 2 - 76 ↔ x ^ 2 - x * y ^ 2 = y ^ 2 - 76 := by
  (intros; ring)
