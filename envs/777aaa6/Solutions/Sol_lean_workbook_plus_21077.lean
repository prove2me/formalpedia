-- Prove2me | solution 1 for lean_workbook_plus_21077
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T02:42:35.107005+00:00
-- url     : https://prove2.me/submissions/a9d69eda-522e-4639-95ce-2ebf2d3c4b1e

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c d n : ℤ) : (a^2 + n * b^2) * (c^2 + n * d^2) = (a * c + n * b * d)^2 + n * (a * d - b * c)^2 := by
  (intros; linarith)
