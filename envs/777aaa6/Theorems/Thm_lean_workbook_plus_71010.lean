-- Prove2me | Theorems.Thm_lean_workbook_plus_71010
-- name    : lean_workbook_plus_71010
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/6f767895-e89a-4dab-9aa6-0703197e71e4
-- statement:
--   Let $x > -1$ and $y = 2$. Prove: $x^2 + 2x \ge xy$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71010 (x : ℝ) (hx : x > -1) (y : ℝ) (hy : y = 2) : x^2 + 2*x ≥ x*y   :=  by sorry
