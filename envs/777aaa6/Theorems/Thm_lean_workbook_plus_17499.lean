-- Prove2me | Theorems.Thm_lean_workbook_plus_17499
-- name    : lean_workbook_plus_17499
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/ad7ee809-40e5-459f-9097-55c3d897ba07
-- statement:
--   Prove: ${\left( {\sum {a^2}} \right)^2} \ge 3\sum {{a^2}{b^2}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17499 (a b c : ℝ) : (a ^ 2 + b ^ 2 + c ^ 2) ^ 2 ≥ 3 * (a ^ 2 * b ^ 2 + b ^ 2 * c ^ 2 + c ^ 2 * a ^ 2)   :=  by sorry
