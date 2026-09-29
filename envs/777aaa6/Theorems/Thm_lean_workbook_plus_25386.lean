-- Prove2me | Theorems.Thm_lean_workbook_plus_25386
-- name    : lean_workbook_plus_25386
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/d8ab1767-4c4d-4e1d-a45b-9b23d3d1d692
-- statement:
--   Given a, b, c are real numbers and $0\le a, b, c \le 1$ , prove that $\frac{a}{1+bc}+\frac{b}{1+ac}+\frac{c}{1+ab} \le 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25386 : ∀ a b c : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 → a / (1 + b * c) + b / (1 + a * c) + c / (1 + a * b) ≤ 1   :=  by sorry
