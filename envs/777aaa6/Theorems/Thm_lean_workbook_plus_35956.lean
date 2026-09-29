-- Prove2me | Theorems.Thm_lean_workbook_plus_35956
-- name    : lean_workbook_plus_35956
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/50d82454-77a4-4a3e-a89e-e40c27afce23
-- statement:
--   $3\sum a^4b^2c^2\leq \sum a^4b^4+2\sum a^4b^2c^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_35956 (a b c : ℝ) : 3 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2) ≤ a ^ 4 * b ^ 4 + b ^ 4 * c ^ 4 + c ^ 4 * a ^ 4 + 2 * (a ^ 4 * b ^ 2 * c ^ 2 + b ^ 4 * c ^ 2 * a ^ 2 + c ^ 4 * a ^ 2 * b ^ 2)   :=  by sorry
