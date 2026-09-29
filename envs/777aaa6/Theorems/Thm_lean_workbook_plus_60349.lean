-- Prove2me | Theorems.Thm_lean_workbook_plus_60349
-- name    : lean_workbook_plus_60349
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/8bb0be8f-2eb6-4b1c-9937-f2c78d32bcaf
-- statement:
--   Well known result: $(a+b)(b+c)(c+a)\geq \frac{8}{9}(a+b+c)(ab+bc+ca)$ and also $(ab+bc+ca)^2\geq 3abc(a+b+c)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_60349 : ∀ a b c : ℝ, (a + b) * (b + c) * (c + a) ≥ (8 / 9) * (a + b + c) * (a * b + b * c + c * a) ∧ (a * b + b * c + c * a) ^ 2 ≥ 3 * a * b * c * (a + b + c)   :=  by sorry
