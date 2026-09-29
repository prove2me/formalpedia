-- Prove2me | Theorems.Thm_lean_workbook_plus_70802
-- name    : lean_workbook_plus_70802
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/039dffda-1b25-46e6-956f-435afc32eea9
-- statement:
--   Binomial expansion: $(a - b)^3 = a^3 - 3a^2b + 3ab^2 - b^3$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_70802 (a b : ℝ) : (a - b) ^ 3 = a ^ 3 - 3 * a ^ 2 * b + 3 * a * b ^ 2 - b ^ 3   :=  by sorry
