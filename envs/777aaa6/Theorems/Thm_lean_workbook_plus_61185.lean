-- Prove2me | Theorems.Thm_lean_workbook_plus_61185
-- name    : lean_workbook_plus_61185
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/10b238d1-df13-4b6f-8f20-0a75575a156c
-- statement:
--   Let $a\geq b\geq c>0.$ Prove that $$(a-b+c)\left(\frac{1}{a+b}-\frac{1}{b+c}+\frac{1}{c+a}\right)\leq\frac{1}{2}.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61185 (a b c : ℝ) (h1 : a ≥ b ∧ b ≥ c ∧ c > 0) :
  (a - b + c) * (1 / (a + b) - 1 / (b + c) + 1 / (c + a)) ≤ 1 / 2   :=  by sorry
