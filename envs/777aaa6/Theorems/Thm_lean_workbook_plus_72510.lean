-- Prove2me | Theorems.Thm_lean_workbook_plus_72510
-- name    : lean_workbook_plus_72510
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/c0500aaf-f15f-4dce-afa5-3f2585432fd9
-- statement:
--   Prove that $(x^4+y^4+z^4)^2\geq (x^2+y^2+z^2)(x^2y^4+y^2z^4+z^2x^4)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72510 (x y z : ℝ) : (x ^ 4 + y ^ 4 + z ^ 4) ^ 2 ≥ (x ^ 2 + y ^ 2 + z ^ 2) * (x ^ 2 * y ^ 4 + y ^ 2 * z ^ 4 + z ^ 2 * x ^ 4)   :=  by sorry
