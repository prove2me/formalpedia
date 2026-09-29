-- Prove2me | Theorems.Thm_lean_workbook_plus_59946
-- name    : lean_workbook_plus_59946
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/ac1f3b11-b461-492b-87e1-c40de3b0b51c
-- statement:
--   By Cauchy-Schwarz: \n $(\frac{a}{b+c})^2+(\frac{b}{c+a})^2+(\frac{c}{a+b})^2\ge{\frac{1}{3}.(\frac{a}{b+c}+\frac{b}{c+a}+\frac{c}{a+b})^2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59946 : ∀ a b c : ℝ, (a / (b + c)) ^ 2 + (b / (c + a)) ^ 2 + (c / (a + b)) ^ 2 ≥ 1 / 3 * (a / (b + c) + b / (c + a) + c / (a + b)) ^ 2   :=  by sorry
