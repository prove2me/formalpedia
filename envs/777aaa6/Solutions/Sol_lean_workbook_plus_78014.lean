-- Prove2me | solution 1 for lean_workbook_plus_78014
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T04:24:34.062769+00:00
-- url     : https://prove2.me/submissions/8c9a8a5b-20b9-49f5-82db-daefdf6c7498

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z : ℝ) (h₁ : x + y + z = 2) (h₂ : x^2 + y^2 + z^2 = 30) (h₃ : x^3 + y^3 + z^3 = 116) : x * y * z = 10 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (y - z), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (y + z)])
