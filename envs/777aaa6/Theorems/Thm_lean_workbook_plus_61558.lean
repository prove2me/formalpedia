-- Prove2me | Theorems.Thm_lean_workbook_plus_61558
-- name    : lean_workbook_plus_61558
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/75d7bd0f-58db-4efe-b22c-0499763d320e
-- statement:
--   $x^5+y^5+z^5\ge3(x^3+y^3+z^3-x^2-y^2-z^2)+x^2+y^2+z^2 \ge x^2+y^2+z^2 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61558 : ∀ x y z : ℝ, x ^ 5 + y ^ 5 + z ^ 5 ≥ 3 * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 - y ^ 2 - z ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 ∧ 3 * (x ^ 3 + y ^ 3 + z ^ 3 - x ^ 2 - y ^ 2 - z ^ 2) + x ^ 2 + y ^ 2 + z ^ 2 ≥ x ^ 2 + y ^ 2 + z ^ 2   :=  by sorry
