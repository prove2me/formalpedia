-- Prove2me | Theorems.Thm_lean_workbook_plus_17055
-- name    : lean_workbook_plus_17055
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/496737ab-018b-4abf-90bf-5086f1a13e15
-- statement:
--   Prove that $8a^3b^3c^3 < (a^2+b^2+c^2)^2(a^2+b^2+c^2 - 8a^2b^2c^2)$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17055 : ∀ a b c : ℝ, 8 * a ^ 3 * b ^ 3 * c ^ 3 < (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 * (a ^ 2 + b ^ 2 + c ^ 2 - 8 * a ^ 2 * b ^ 2 * c ^ 2)   :=  by sorry
