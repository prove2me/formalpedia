-- Prove2me | Theorems.Thm_lean_workbook_plus_71687
-- name    : lean_workbook_plus_71687
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/92c830cd-f88e-4108-ab8d-70fc6ac024cd
-- statement:
--   Prove: $${\left(a+b+c\right)}^5\geq27{\left(a^2b+b^2c+c^2a\right)}{\left(ab+bc+ca\right)}\text.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_71687 ∀ a b c : ℝ, (a + b + c) ^ 5 ≥ 27 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) * (a * b + b * c + c * a)   :=  by sorry
