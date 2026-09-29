-- Prove2me | solution 1 for lean_workbook_plus_27294
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:03:58.703298+00:00
-- url     : https://prove2.me/submissions/e1aecce3-5be2-450c-b49d-71f93192ee00

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b : ℝ) : a^3 - b^3 = (a - b) * (a^2 + a * b + b^2) := by
  (intros; linarith)
