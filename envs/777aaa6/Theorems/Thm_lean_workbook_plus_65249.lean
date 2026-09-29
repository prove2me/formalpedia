-- Prove2me | Theorems.Thm_lean_workbook_plus_65249
-- name    : lean_workbook_plus_65249
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.755244+00:00
-- url     : https://prove2.me/theorems/b35bbfd8-aea1-43a2-a30a-07e07cf1d308
-- statement:
--   Apply Holder inequality: ${{\left( \frac{{{a}^{2}}}{b}+\frac{{{b}^{2}}}{c}+\frac{{{c}^{2}}}{a} \right)}^{2}}\left( {{a}^{2}}{{b}^{2}}+{{b}^{2}}{{c}^{2}}+{{c}^{2}}{{a}^{2}} \right)\ge {{\left( {{a}^{2}}+{{b}^{2}}+{{c}^{2}} \right)}^{3}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_65249 : ∀ a b c : ℝ, (a^2 / b + b^2 / c + c^2 / a)^2 * (a^2 * b^2 + b^2 * c^2 + c^2 * a^2) ≥ (a^2 + b^2 + c^2)^3   :=  by sorry
