-- Prove2me | Theorems.Thm_lean_workbook_plus_1048
-- name    : lean_workbook_plus_1048
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f7d59f04-ee2c-47be-988c-5d496d7ff8f3
-- statement:
--   Id est, $\frac{1}{9}(2a^2+2c^2-b^2+2a^2+2b^2-c^2)=a^2$ , which gives $b^2+c^2=5a^2$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1048 (a b c : ℝ) : (1 / 9) * (2 * a ^ 2 + 2 * c ^ 2 - b ^ 2 + 2 * a ^ 2 + 2 * b ^ 2 - c ^ 2) = a ^ 2 ↔ b ^ 2 + c ^ 2 = 5 * a ^ 2   :=  by sorry
