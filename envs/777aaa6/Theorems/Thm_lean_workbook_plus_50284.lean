-- Prove2me | Theorems.Thm_lean_workbook_plus_50284
-- name    : lean_workbook_plus_50284
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a94b7e8b-aa15-4c5e-949f-6dac3b882357
-- statement:
--   Explain how to rewrite the equation $x^9 - 37x^8 - 2x^7 + 74x^6 + x^4 - 37x^3 - 2x^2 + 74x$ as $x(x^5+1)(x^3-37x^2-2x+74)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_50284 (x : ℝ) : x^9 - 37*x^8 - 2*x^7 + 74*x^6 + x^4 - 37*x^3 - 2*x^2 + 74*x = x * (x^5 + 1) * (x^3 - 37*x^2 - 2*x + 74)   :=  by sorry
