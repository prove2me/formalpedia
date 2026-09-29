-- Prove2me | solution 1 for lean_workbook_plus_31657
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:44:34.127374+00:00
-- url     : https://prove2.me/submissions/7e0daf89-4fa3-48fe-8a4d-6da8737e5276

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x : ℝ) (hx : x^2 ≤ 1) : 1 - x^2 ≤ 2 * (1 - x) := by
  (intros; nlinarith [sq_nonneg (x)])
