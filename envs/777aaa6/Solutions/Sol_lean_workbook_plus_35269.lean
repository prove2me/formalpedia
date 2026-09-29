-- Prove2me | solution 1 for lean_workbook_plus_35269
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:17:41.658639+00:00
-- url     : https://prove2.me/submissions/24213203-7488-4f67-80ee-ebba70a50252

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (h₁ : 17^2 + 17 * 7 + 7^2 = 457) : 17^2 + 17 * 7 + 7^2 = 457 := by
  norm_num
