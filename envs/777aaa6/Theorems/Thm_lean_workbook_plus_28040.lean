-- Prove2me | Theorems.Thm_lean_workbook_plus_28040
-- name    : lean_workbook_plus_28040
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/95d1f929-009f-4ccb-a066-f772b37a5e13
-- statement:
--   Prove that $\sin 1 > \frac{1}{\sqrt[4]{2}}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28040 : Real.sin 1 > 1 / (2 : ℝ) ^ (1 / 4)   :=  by sorry
