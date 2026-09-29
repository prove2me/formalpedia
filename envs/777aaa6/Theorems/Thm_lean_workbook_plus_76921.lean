-- Prove2me | Theorems.Thm_lean_workbook_plus_76921
-- name    : lean_workbook_plus_76921
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/0d4e268a-4b0f-4dae-85a9-fa5fb372b4a2
-- statement:
--   For non negative real numbers $x$ and $y$ , prove that \n $$\{5x\}+\{5y\}=\{3x+y\}+\{3y+x\}$$ where $\{x\}$ is the fractional part of $x$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_76921 (x y : ℝ) : (5*x) % 1 + (5*y) % 1 = (3*x + y) % 1 + (3*y + x) % 1   :=  by sorry
