-- Prove2me | Theorems.Thm_lean_workbook_plus_8162
-- name    : lean_workbook_plus_8162
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/ec570760-2aee-4e99-9dbc-1493d94b694c
-- statement:
--   Prove $ e^t > t + 1$ for $ t > 0$ and use it to show $ e^x > 1 + x + \frac{x^2}{2!} + \cdots + \frac{x^n}{n!} + \cdots$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8162 (t : ℝ) (ht : t > 0) : exp t > t + 1   :=  by sorry
