-- Prove2me | Theorems.Thm_lean_workbook_plus_16245
-- name    : lean_workbook_plus_16245
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/dfc3259d-857b-4c00-b71f-8cbff3783298
-- statement:
--   By AM-GM, we have the simple inequality: $3\sum_{cyc}{xy}\leq (x + y + z)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16245 (x y z : ℝ) : 3 * (x * y + y * z + z * x) ≤ (x + y + z) ^ 2   :=  by sorry
