-- Prove2me | solution 1 for lean_workbook_plus_28568
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:41:24.420399+00:00
-- url     : https://prove2.me/submissions/94a84190-9924-45fd-8d3f-5bde6326c937

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (n B : ℤ)
  (h₀ : n = -8)
  (h₁ : -4 * B = 12) :
  B = -3 := by
  (intros; omega)
