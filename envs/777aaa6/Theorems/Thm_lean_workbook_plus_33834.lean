-- Prove2me | Theorems.Thm_lean_workbook_plus_33834
-- name    : lean_workbook_plus_33834
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/6e972ad6-11cc-4a8c-bef8-304233836c78
-- statement:
--   If $a>0, b>0, c>0$ such that $a^2+b^2+c^2=\frac{1}{3}$ prove the inequality $$(a+b+c)(1+\frac{1}{abc}) \geq 28.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_33834 (a b c : ℝ) (ha : a > 0) (hb : b > 0) (hc : c > 0) (habc : a * b * c = 1) (h : a^2 + b^2 + c^2 = 1 / 3) : (a + b + c) * (1 + 1 / a / b / c) ≥ 28   :=  by sorry
