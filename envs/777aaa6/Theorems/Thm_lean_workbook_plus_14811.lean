-- Prove2me | Theorems.Thm_lean_workbook_plus_14811
-- name    : lean_workbook_plus_14811
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/5d906b61-303d-4c85-a9ee-c5ff86ee9ead
-- statement:
--   Let $a,b,c\in \mathbb{R}$ with $a+b-c=5,a-b+c=7.$ Calculated ${{a}^{2}}+{{b}^{2}}+{{c}^{2}}-2bc.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_14811 (a b c : ℝ) (h₁ : a + b - c = 5) (h₂ : a - b + c = 7) : a^2 + b^2 + c^2 - 2 * b * c = 37   :=  by sorry
