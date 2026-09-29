-- Prove2me | solution 1 for lean_workbook_plus_9599
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:38:55.997716+00:00
-- url     : https://prove2.me/submissions/808bf5fa-c393-4f53-887f-719243738ec5

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ)
  (h₀ : 0 < x ∧ 0 < y ∧ 0 < z) :
  x^4 + y^4 + z^4 ≥ x^3 * y + y^3 * z + z^3 * x := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
