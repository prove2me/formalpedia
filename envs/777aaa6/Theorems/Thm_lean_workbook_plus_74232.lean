-- Prove2me | Theorems.Thm_lean_workbook_plus_74232
-- name    : lean_workbook_plus_74232
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f9d1d42e-e7a5-4b27-91f0-f36a331cc999
-- statement:
--   For non negative real numbers $x$ and $y$ , prove that \n $$\{5x\}+\{5y\}\ge\{3x+y\}+\{3y+x\}$$ where $\{x\}$ is the fractional part of $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74232 (x y : ℝ) : (5*x) % 1 + (5*y) % 1 ≥ (3*x + y) % 1 + (3*y + x) % 1   :=  by sorry
