-- Prove2me | Theorems.Thm_lean_workbook_plus_920
-- name    : lean_workbook_plus_920
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/44b59e9b-c12d-447a-a5b1-bdb6a12179e4
-- statement:
--   Does the inequality $2\left(ab+bc+cd+da+ac+bd\right)\leq a+b+c+d+k\left(abc+abd+acd+bcd\right)$ always hold, for $k<3$?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_920 : ∀ a b c d k : ℝ, k < 3 → 2 * (a * b + b * c + c * d + d * a + a * c + b * d) ≤ a + b + c + d + k * (a * b * c + a * b * d + a * c * d + b * c * d)   :=  by sorry
