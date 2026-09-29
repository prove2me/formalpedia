-- Prove2me | Theorems.Thm_lean_workbook_plus_51082
-- name    : lean_workbook_plus_51082
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.108955+00:00
-- url     : https://prove2.me/theorems/a1105f5c-0c4c-4908-9307-0890d4670b21
-- statement:
--   Prove that $\frac{x}{x^2 + 1} \le -\frac{3}{10}$ for $-3 \le x \le -\frac{1}{3}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51082 (x : ℝ) (hx1 : -3 ≤ x) (hx2 : x ≤ -1/3) : x / (x^2 + 1) ≤ -3/10   :=  by sorry
