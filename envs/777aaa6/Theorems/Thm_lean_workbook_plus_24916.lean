-- Prove2me | Theorems.Thm_lean_workbook_plus_24916
-- name    : lean_workbook_plus_24916
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/0550411e-026a-44c5-8d78-45992624696f
-- statement:
--   Prove that $y^{y-1} \geq 1$ for $y \geq 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_24916 (y : ℝ) (hy : 1 ≤ y) : y ^ (y - 1) ≥ 1   :=  by sorry
