-- Prove2me | Theorems.Thm_lean_workbook_plus_20808
-- name    : lean_workbook_plus_20808
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5fe231c7-f583-4f49-a3ce-de86597104bc
-- statement:
--   prove that $ab(b+c)^2+bc(a+b)^2\le\frac{(a+b)^2(b+c)^2}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_20808 (a b c : ℝ) : a * b * (b + c) ^ 2 + b * c * (a + b) ^ 2 ≤ (a + b) ^ 2 * (b + c) ^ 2 / 2   :=  by sorry
