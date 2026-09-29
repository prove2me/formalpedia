-- Prove2me | Theorems.Thm_lean_workbook_plus_65462
-- name    : lean_workbook_plus_65462
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/f224f3d3-9950-4c59-b891-e4deb4fcdd11
-- statement:
--   Prove that $\frac{27(2a+1)}{25}-\frac{1}{2a^2-2a+1}\geq 0$ for $a > 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65462 (h : 0 < a) : (27 * (2 * a + 1) / 25 - 1 / (2 * a ^ 2 - 2 * a + 1)) ≥ 0   :=  by sorry
