-- Prove2me | solution 1 for lean_workbook_plus_24734
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:26.767563+00:00
-- url     : https://prove2.me/submissions/b991d29e-494d-4003-b65a-fa22844bf287

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (A : Matrix (Fin 4) (Fin 4) ℤ) : ∑ i : Fin 4, ∑ j : Fin 4, (i - j) ^ 2 = 40 := by
  decide
