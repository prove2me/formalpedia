-- Prove2me | Theorems.Thm_lean_workbook_plus_5029
-- name    : lean_workbook_plus_5029
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/255d26ea-bcd0-4d81-bf38-e7d0d2a5042b
-- statement:
--   Prove that $3 \sin a - 4 \sin^{3}a = \sin 3a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5029 (a : ℝ) : 3 * Real.sin a - 4 * (Real.sin a)^3 = Real.sin (3 * a)   :=  by sorry
