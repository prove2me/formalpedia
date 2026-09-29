-- Prove2me | Theorems.Thm_lean_workbook_plus_19421
-- name    : lean_workbook_plus_19421
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.799204+00:00
-- url     : https://prove2.me/theorems/54dd4db5-6747-4d3a-aad4-0c5104df17cd
-- statement:
--   $(1+\frac{1}{a})(1+\frac{1}{b})(1+\frac{1}{c})=1+\frac{1}{a}+\frac{1}{b}+\frac{1}{c}+\frac{2}{abc}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_19421 : ∀ a b c : ℝ, (1 + 1 / a) * (1 + 1 / b) * (1 + 1 / c) = 1 + 1 / a + 1 / b + 1 / c + 2 / (a * b * c)   :=  by sorry
