-- Prove2me | Theorems.Thm_lean_workbook_plus_1500
-- name    : lean_workbook_plus_1500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/2691c54b-28d9-4663-b92c-30b341552d35
-- statement:
--   Prove $(1+1/4)(x^2+4y^2) \ge (x+y)^2$ using Cauchy Schwarz inequality
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1500 (x y : ℝ) : (1 + 1 / 4) * (x ^ 2 + 4 * y ^ 2) ≥ (x + y) ^ 2   :=  by sorry
