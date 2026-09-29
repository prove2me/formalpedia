-- Prove2me | solution 1 for lean_workbook_plus_39044
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:41:55.462602+00:00
-- url     : https://prove2.me/submissions/c814c1fa-4e3c-4588-97a6-d56d48b1c8f9

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (x y : ℝ) : 2 * (x ^ 2 + y ^ 2) ≥ (x + y) ^ 2 := by
  (intros; nlinarith [sq_nonneg (x), sq_nonneg (y), sq_nonneg (x - y), sq_nonneg (x + y)])
