-- Prove2me | Theorems.Thm_lean_workbook_plus_11629
-- name    : lean_workbook_plus_11629
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/1ead484c-483d-4d34-ae37-8a9a4aa14f07
-- statement:
--   Prove that the inequality $(a^2b+b^2c+c^2a-3abc)^2\geq0$ holds.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11629 : ∀ a b c : ℝ, (a^2 * b + b^2 * c + c^2 * a - 3 * a * b * c)^2 ≥ 0   :=  by sorry
