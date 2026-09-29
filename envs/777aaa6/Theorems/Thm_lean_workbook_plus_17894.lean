-- Prove2me | Theorems.Thm_lean_workbook_plus_17894
-- name    : lean_workbook_plus_17894
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/5d16872a-7f9b-4f46-830d-31ac58c8165c
-- statement:
--   Prove the inequality $\frac{a}{1+a}+\frac{b}{1+b} \ge \frac{a+b}{1+a+b}$ for all non-negative $a,b$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17894 (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : (a / (1 + a) + b / (1 + b)) ≥ (a + b) / (1 + a + b)   :=  by sorry
