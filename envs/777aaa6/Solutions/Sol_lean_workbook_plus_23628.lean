-- Prove2me | solution 1 for lean_workbook_plus_23628
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:55:31.82821+00:00
-- url     : https://prove2.me/submissions/a8cc2901-82da-49a3-8f1c-3f25db2ea3cc

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y z t : ℝ)
  (h₀ : x^2 + y^2 = 9)
  (h₁ : z^2 + t^2 = 4)
  (h₂ : x * z = y * t) :
  9 * 4 ≥ 4 * x * y * z * t := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (z), sq_nonneg (t), sq_nonneg (x - y), sq_nonneg (x - z), sq_nonneg (x - t), sq_nonneg (y - z), sq_nonneg (y - t), sq_nonneg (z - t), sq_nonneg (x + y), sq_nonneg (x + z), sq_nonneg (x + t), sq_nonneg (y + z), sq_nonneg (y + t), sq_nonneg (z + t)])
