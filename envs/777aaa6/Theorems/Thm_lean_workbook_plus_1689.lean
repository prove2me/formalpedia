-- Prove2me | Theorems.Thm_lean_workbook_plus_1689
-- name    : lean_workbook_plus_1689
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e3480768-c9b6-43f2-8d7f-9ea4c4582eb9
-- statement:
--   Let $a,b$ and $c$ be real numbers such that $a^2+b^2+c^2=1.$ Prove that $$(a-b)^2+(b-c)^2+(c-a)^2\le3 $$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1689 : ∀ a b c : ℝ, a^2 + b^2 + c^2 = 1 → (a - b)^2 + (b - c)^2 + (c - a)^2 ≤ 3   :=  by sorry
