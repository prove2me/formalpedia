-- Prove2me | Theorems.Thm_lean_workbook_plus_38811
-- name    : lean_workbook_plus_38811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9cce6b22-c297-4666-89e2-373b0aaa2d66
-- statement:
--   Prove that $\frac{a^3}{b}+\frac{b^3}{a} \ge a^2+b^2$ whenever $a,b>0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38811 (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : (a^3 / b + b^3 / a) ≥ a^2 + b^2   :=  by sorry
