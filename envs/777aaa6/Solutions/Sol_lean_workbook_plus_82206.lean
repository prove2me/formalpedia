-- Prove2me | solution 1 for lean_workbook_plus_82206
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T03:35:48.272942+00:00
-- url     : https://prove2.me/submissions/6d5bb9ef-b00c-4bdc-8521-964f36d84ade

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ)
  (h₀ : x^2 + y^2 = 1) :
  (x + y)^2 ≤ 2 * (x^2 + y^2) := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
