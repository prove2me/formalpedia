-- Prove2me | Theorems.Thm_lean_workbook_plus_48244
-- name    : lean_workbook_plus_48244
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/949c5ee5-c3f3-41e8-a950-0bb587ee9b57
-- statement:
--   Prove the inequality for four variables: $4(ab+bc+cd+da) \le (a+b+c+d)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_48244 (a b c d : ℝ) : 4 * (a * b + b * c + c * d + d * a) ≤ (a + b + c + d) ^ 2   :=  by sorry
