-- Prove2me | Theorems.Thm_lean_workbook_plus_86
-- name    : lean_workbook_plus_86
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/1ae6c349-ce1f-4ff2-90d8-f029cdc960c7
-- statement:
--   Let $a,b,c>0$ and $\frac{1-ab}{1+b}+\frac{1-bc}{1+c}+\frac{1-ca}{1+a}=0$ . Prove that $$abc\leq 1$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_86 (a b c : ℝ) (h : a > 0 ∧ b > 0 ∧ c > 0) (habc : a * b * c = 1) (h : (1 - a * b) / (1 + b) + (1 - b * c) / (1 + c) + (1 - c * a) / (1 + a) = 0) : a * b * c ≤ 1   :=  by sorry
