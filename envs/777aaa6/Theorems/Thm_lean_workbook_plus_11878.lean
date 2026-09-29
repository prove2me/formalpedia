-- Prove2me | Theorems.Thm_lean_workbook_plus_11878
-- name    : lean_workbook_plus_11878
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/9f961f20-72ed-4608-9de4-8db0438165d3
-- statement:
--   Prove that $2x^4 - x^3 + x^2 - x - 1 > 0$ for $ x > 1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11878 : ∀ x : ℝ, 1 < x → 2 * x ^ 4 - x ^ 3 + x ^ 2 - x - 1 > 0   :=  by sorry
