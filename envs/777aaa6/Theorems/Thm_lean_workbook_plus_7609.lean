-- Prove2me | Theorems.Thm_lean_workbook_plus_7609
-- name    : lean_workbook_plus_7609
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/8225a00e-b722-4771-b3e1-7f1a4f366114
-- statement:
--   Prove that $\sin 3a=-4\sin^3 a + 3\sin a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7609 (a : ℝ) : Real.sin (3 * a) = -4 * (Real.sin a)^3 + 3 * (Real.sin a)   :=  by sorry
