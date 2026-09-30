-- Prove2me | solution 2 for lean_workbook_plus_12536
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T13:31:43.573118+00:00
-- url     : https://prove2.me/submissions/d99b6ff3-88cf-4f10-be8c-b98c7a1ecd47

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution {a b c d : ℝ} : (a ^ 2 + d ^ 2) * (c ^ 2 + b ^ 2) = (a * b + c * d) ^ 2 + (a * c - b * d) ^ 2 := by
  (intros; linarith)
