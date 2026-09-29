-- Prove2me | Theorems.Thm_lean_workbook_plus_22430
-- name    : lean_workbook_plus_22430
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/b8dbc4d9-dfec-4f83-ba5c-25c7c7b0fc90
-- statement:
--   Prove that $8{a^4} + 8{a^3} - 5{a^2} - 4a + 3 > 0$ with $a = \sin t;t \in R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22430 (a : ℝ) (ha : a = Real.sin t) : 8 * a ^ 4 + 8 * a ^ 3 - 5 * a ^ 2 - 4 * a + 3 > 0   :=  by sorry
