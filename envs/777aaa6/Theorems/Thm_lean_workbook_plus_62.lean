-- Prove2me | Theorems.Thm_lean_workbook_plus_62
-- name    : lean_workbook_plus_62
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ee2587b1-5f59-4da0-89c3-85953fbfe418
-- statement:
--   $3(a^2b+b^2c+c^2a)\leq (ab+bc+ca)^2\leq 9$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62 : ∀ a b c : ℝ, 3 * (a ^ 2 * b + b ^ 2 * c + c ^ 2 * a) ≤ (a * b + b * c + c * a) ^ 2 ∧ (a * b + b * c + c * a) ^ 2 ≤ 9   :=  by sorry
