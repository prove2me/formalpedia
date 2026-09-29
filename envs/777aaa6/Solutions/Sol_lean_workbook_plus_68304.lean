-- Prove2me | solution 1 for lean_workbook_plus_68304
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:02:02.913282+00:00
-- url     : https://prove2.me/submissions/8fbcc626-0506-4689-aff2-65d715e45cb6

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 3880 ≠ 0) (h₂ : 1990 ≠ 0) : (444444444444444444444444444444444444444444444444 - 888888888888888888888888888888888888888888888888) = -444444444444444444444444444444444444444444444444 := by
  norm_num
