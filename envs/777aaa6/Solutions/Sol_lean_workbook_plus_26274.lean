-- Prove2me | solution 1 for lean_workbook_plus_26274
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:26:08.069913+00:00
-- url     : https://prove2.me/submissions/17d4fc88-28a4-472c-b530-fd00386903af

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d e f : ℝ)
  (h₀ : a + b + c + d + e = f) :
  a + b + c + d + e = f := by
  (intros; simp_all)
