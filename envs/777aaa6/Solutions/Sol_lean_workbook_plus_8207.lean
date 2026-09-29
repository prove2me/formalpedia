-- Prove2me | solution 1 for lean_workbook_plus_8207
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:57:31.316276+00:00
-- url     : https://prove2.me/submissions/77a622d2-362e-475c-b8d8-89be472e85d8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x ≠ 0)
  (h₁ : y ≠ 0) :
  (x + 1/x) * (y + 1/y) + (x - 1/x) * (y - 1/y) = 2 * x * y + 2 / (x * y) := by
  (intros; ring)
