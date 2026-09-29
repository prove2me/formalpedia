-- Prove2me | Theorems.Thm_lean_workbook_plus_25346
-- name    : lean_workbook_plus_25346
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/8f93df64-aeb5-4f1e-90d9-c46ac7c05d1f
-- statement:
--   Prove that \n\n $ ab(a^4 + b^4) + 2ab \ge 2ab(a^2 + b^2)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25346 : ∀ a b : ℝ, a * b * (a ^ 4 + b ^ 4) + 2 * a * b ≥ 2 * a * b * (a ^ 2 + b ^ 2)   :=  by sorry
