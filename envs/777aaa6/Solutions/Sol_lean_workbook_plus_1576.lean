-- Prove2me | solution 1 for lean_workbook_plus_1576
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T14:24:08.312845+00:00
-- url     : https://prove2.me/submissions/c41df989-6808-4697-ae70-361b126fd9c8

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c : ℝ) (h : a + b + c = 0) : a^3 + b^3 + c^3 - 3 * a * b * c = 1 / 2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2) := by
  (intros; linarith)
