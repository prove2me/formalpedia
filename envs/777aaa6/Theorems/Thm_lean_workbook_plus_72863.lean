-- Prove2me | Theorems.Thm_lean_workbook_plus_72863
-- name    : lean_workbook_plus_72863
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/789a0ebb-b1d2-4d19-a7af-780aa545f634
-- statement:
--   Show that $t - 1 - \ln(t) \geq 0$ for all $t > 0$ using calculus.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72863 (t : ℝ) (ht : t > 0) : t - 1 - Real.log t ≥ 0   :=  by sorry
