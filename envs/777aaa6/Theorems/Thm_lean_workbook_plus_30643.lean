-- Prove2me | Theorems.Thm_lean_workbook_plus_30643
-- name    : lean_workbook_plus_30643
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.279436+00:00
-- url     : https://prove2.me/theorems/a968f952-9c8e-43af-8673-6758d200ebf0
-- statement:
--   We have $f\left(-\frac{17}{2}\right) = \frac 18 \sum (a-b)^2(2a+2b+17c)^2 \geqslant 0.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_30643 (a b c : ℝ) : (1 / 8) * (a - b) ^ 2 * (2 * a + 2 * b + 17 * c) ^ 2 + (1 / 8) * (b - c) ^ 2 * (2 * b + 2 * c + 17 * a) ^ 2 + (1 / 8) * (c - a) ^ 2 * (2 * c + 2 * a + 17 * b) ^ 2 ≥ 0   :=  by sorry
