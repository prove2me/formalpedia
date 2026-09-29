-- Prove2me | Theorems.Thm_lean_workbook_plus_6973
-- name    : lean_workbook_plus_6973
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/628b93b6-455c-408f-8b96-c7eb35e2e90a
-- statement:
--   $-\sin(a+2b)\sin a + \sin^2a = 0$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_6973 : ∀ a b : ℝ, -Real.sin (a + 2 * b) * Real.sin a + (Real.sin a)^2 = 0   :=  by sorry
