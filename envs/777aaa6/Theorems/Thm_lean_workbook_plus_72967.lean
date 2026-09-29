-- Prove2me | Theorems.Thm_lean_workbook_plus_72967
-- name    : lean_workbook_plus_72967
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/fbe27e0b-71af-4910-987c-1cd2f560cc52
-- statement:
--   $$\dfrac{a}{b^2+c^2}+\dfrac{b}{c^2+a^2}+\dfrac{c}{a^2+b^2}\geq \dfrac{4}{5}\left(\dfrac{1}{a+b}+\dfrac{1}{b+c}+\dfrac{1}{c+a}\right)+\dfrac{81abc}{10(a+b+c)^2(ab+bc+ca)}$$ is also true.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72967 : ∀ a b c : ℝ, (a / (b ^ 2 + c ^ 2) + b / (c ^ 2 + a ^ 2) + c / (a ^ 2 + b ^ 2) ≥ 4 / 5 * (1 / (a + b) + 1 / (b + c) + 1 / (c + a)) + 81 * a * b * c / (10 * (a + b + c) ^ 2 * (a * b + b * c + c * a)))   :=  by sorry
