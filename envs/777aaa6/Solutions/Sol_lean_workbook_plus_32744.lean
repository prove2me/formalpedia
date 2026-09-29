-- Prove2me | solution 1 for lean_workbook_plus_32744
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T11:05:43.412371+00:00
-- url     : https://prove2.me/submissions/7c9c3b36-5047-4cd9-ab4b-d4684ba62e32

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) : 2 * a * b * c * (2 * (a ^ 2 + b ^ 2 + c ^ 2) + b ^ 2 + c ^ 2 + b * c) = a * b * c * (4 * (a ^ 2 + b ^ 2 + c ^ 2) + 2 * (b ^ 2 + c ^ 2 + b * c)) := by
  (intros; linarith)
