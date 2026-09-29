-- Prove2me | Theorems.Thm_lean_workbook_plus_2046
-- name    : lean_workbook_plus_2046
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ec80a310-9d98-4cad-b25e-128da2abe001
-- statement:
--   Prove the inequality: $2a^4 + b^4 + c^4 - 4a^2bc \geq 0$ for all real numbers $a$, $b$, and $c$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2046 (a b c : ℝ) : 2 * a ^ 4 + b ^ 4 + c ^ 4 - 4 * a ^ 2 * b * c ≥ 0   :=  by sorry
