-- Prove2me | Theorems.Thm_lean_workbook_plus_35127
-- name    : lean_workbook_plus_35127
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/fdd9d9ef-79a5-4f14-b46f-2527c490a890
-- statement:
--   Prove that $\frac{1}{1+x^2}\geq\frac{2-x}{2}$ for all $x\geq0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35127 (x : ℝ) (hx : 0 ≤ x) : 1 / (1 + x ^ 2) ≥ (2 - x) / 2   :=  by sorry
