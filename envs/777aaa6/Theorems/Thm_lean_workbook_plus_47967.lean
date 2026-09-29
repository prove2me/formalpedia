-- Prove2me | Theorems.Thm_lean_workbook_plus_47967
-- name    : lean_workbook_plus_47967
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/35761c47-7bbc-4ba8-be80-4d8d3152bed0
-- statement:
--   $\Rightarrow x\leqslant 1$ and $x\geq -1$ (since $ x^4+y^4=1$ )
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47967 (x y : ℝ) (h : x^4 + y^4 = 1) : -1 ≤ x ∧ x ≤ 1   :=  by sorry
