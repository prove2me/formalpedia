-- Prove2me | solution 1 for lean_workbook_plus_37212
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:37:44.960371+00:00
-- url     : https://prove2.me/submissions/11dc3c2d-5b31-40c4-877b-831c56015e69

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (q : ℤ) (h : q % 2 = 1) : (3 * q - 1) % 4 = 0 ∨ (3 * q + 1) % 4 = 0 := by
  (intros; omega)
