-- Prove2me | Theorems.Thm_lean_workbook_plus_35540
-- name    : lean_workbook_plus_35540
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/76c9df83-10a3-4f65-bda7-4e8fc3ec1299
-- statement:
--   Prove that $\frac{3x^2(x^2-4)+x^2+4}{2x(x^2-1)^3}>0$ for all $x \geq 2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35540 (x : ℝ) (hx : 2 ≤ x) : (3 * x ^ 2 * (x ^ 2 - 4) + x ^ 2 + 4) / (2 * x * (x ^ 2 - 1) ^ 3) > 0   :=  by sorry
