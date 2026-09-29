-- Prove2me | Theorems.Thm_lean_workbook_plus_1663
-- name    : lean_workbook_plus_1663
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/cb8bdd7c-17b7-450f-a6f1-e1adc3cdcc03
-- statement:
--   Prove that: \n Easily we have: ${(x + y + z)^2} \ge 3(xy + yz + zx)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1663 (x y z : ℝ) : (x + y + z) ^ 2 ≥ 3 * (x*y + y*z + z*x)   :=  by sorry
