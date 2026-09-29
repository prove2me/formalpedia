-- Prove2me | Theorems.Thm_lean_workbook_plus_55257
-- name    : lean_workbook_plus_55257
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/db6b7b7b-66c8-4197-99dc-9689c59d70eb
-- statement:
--   $\frac{a}{{{a}^{3}}+{{b}^{2}}+c}+\frac{b}{{{b}^{3}}+{{c}^{2}}+a}+\frac{c}{{{c}^{3}}+{{a}^{2}}+b}\le 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_55257 : ∀ a b c : ℝ, (a / (a ^ 3 + b ^ 2 + c) + b / (b ^ 3 + c ^ 2 + a) + c / (c ^ 3 + a ^ 2 + b) : ℝ) ≤ 1   :=  by sorry
