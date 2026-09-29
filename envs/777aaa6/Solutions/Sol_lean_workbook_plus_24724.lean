-- Prove2me | solution 1 for lean_workbook_plus_24724
-- status  : ACCEPTED   (prove)
-- author  : @evgeth
-- created : 2026-09-05T12:34:53.270291+00:00
-- url     : https://prove2.me/submissions/acd9f3ab-5096-4fd4-8299-0f7f58071a9f

import Mathlib.Analysis.Complex.Basic

set_option autoImplicit false

theorem solution (a b c x : ℝ) (hx : abs x ≤ 1) (h1 : abs (a * x ^ 2 + b * x + c) ≤ 1) (h2 : abs (a * 0 ^ 2 + b * 0 + c) ≤ 1) (h3 : abs (a * (-1) ^ 2 + b * (-1) + c) ≤ 1) : abs (a * x ^ 2 + b * x + c) ≤ 5 / 4 := by
  (intros; linarith)
