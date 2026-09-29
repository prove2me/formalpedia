-- Prove2me | Theorems.Thm_lean_workbook_plus_1576
-- name    : lean_workbook_plus_1576
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/074fb5ad-ebf2-4adf-b157-2ef422d2cd76
-- statement:
--   Prove that $a^3+b^3+c^3-3abc = \frac{1}{2}(a+b+c)((a-b)^2 + (b-c)^2 + (c-a)^2)$ given $a+b+c=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1576 (a b c : ℝ) (h : a + b + c = 0) : a^3 + b^3 + c^3 - 3 * a * b * c = 1 / 2 * (a + b + c) * ((a - b)^2 + (b - c)^2 + (c - a)^2)   :=  by sorry
