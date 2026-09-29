-- Prove2me | Theorems.Thm_lean_workbook_plus_61669
-- name    : lean_workbook_plus_61669
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/71f7f2a0-dffe-4694-8dc8-d106052cc3eb
-- statement:
--   With conditions $a,b,c\in{[0,1]},a+b+c=\frac{3}{2}$ ,We have $\frac{3}{4}-(ab+bc+ca)=\sum{\frac{(a-b)^2}{6}}\ge{0}$ $ab+bc+ca-\frac{1}{2}=(1-a)(1-b)(1-c)+abc\ge{0}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61669 : ∀ a b c : ℝ, a ∈ Set.Icc 0 1 ∧ b ∈ Set.Icc 0 1 ∧ c ∈ Set.Icc 0 1 ∧ a + b + c = 3 / 2 → 3 / 4 - (a * b + b * c + c * a) = (a - b) ^ 2 / 6 + (b - c) ^ 2 / 6 + (c - a) ^ 2 / 6 ∧ a * b + b * c + c * a - 1 / 2 = (1 - a) * (1 - b) * (1 - c) + a * b * c   :=  by sorry
