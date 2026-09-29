-- Prove2me | solution 1 for lean_workbook_plus_37301
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T10:53:58.224381+00:00
-- url     : https://prove2.me/submissions/32a5ef18-b499-47ac-8681-f47bd49a8d48

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution :  ∀ a b c : ℝ, 2 * (a ^ 2 + b ^ 2) * (b ^ 2 + c ^ 2) * (c ^ 2 + a ^ 2) - (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a + a ^ 2 * c + c ^ 2 * b + b ^ 2 * a - 2 * a * b * c) ^ 2 = (a - b) ^ 2 * (b - c) ^ 2 * (c - a) ^ 2 := by
  (intros; linarith)
