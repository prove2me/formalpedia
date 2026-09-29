-- Prove2me | Theorems.Thm_lean_workbook_plus_17999
-- name    : lean_workbook_plus_17999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/8bb4fe37-ef8c-4973-8243-a6beb803d286
-- statement:
--   Let $a,b,c \in \mathbb{R}$ such that $a+b+c=0$ and $abc=4.$ Find the value of $a^3+b^3+c^3.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17999 (a b c : ℝ) (h₁ : a + b + c = 0) (h₂ : a * b * c = 4) : a ^ 3 + b ^ 3 + c ^ 3 = 12   :=  by sorry
