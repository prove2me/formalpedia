-- Prove2me | solution 1 for lean_workbook_plus_19295
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:43:52.856987+00:00
-- url     : https://prove2.me/submissions/0d3e428d-0eb3-4a5a-bc67-0085213113fb

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (b c : ℤ)
  (h₀ : b^3 - 4 * b * c + c^3 = -1) :
  27 * b^3 + 27 * c^3 - 108 * b * c + 64 = 37 := by
  (intros; linarith)
