-- Prove2me | Theorems.Thm_lean_workbook_plus_40215
-- name    : lean_workbook_plus_40215
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/0adfdac1-8105-4c08-9598-4d9dadb6f91a
-- statement:
--   Prove that $(x^3+y^3+z^3)^2\geq3(x^3y^3+x^3z^3+y^3z^3)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40215 (x y z : ℝ) : (x ^ 3 + y ^ 3 + z ^ 3) ^ 2 ≥ 3 * (x ^ 3 * y ^ 3 + x ^ 3 * z ^ 3 + y ^ 3 * z ^ 3)   :=  by sorry
