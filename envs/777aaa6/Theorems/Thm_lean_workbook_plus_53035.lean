-- Prove2me | Theorems.Thm_lean_workbook_plus_53035
-- name    : lean_workbook_plus_53035
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/649f00c9-6ee4-41b8-a388-4aca93c953eb
-- statement:
--   Prove that $\sin 3a = 3\sin a - 4 \sin^{3}a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_53035 (a : ℝ) : Real.sin (3 * a) = 3 * Real.sin a - 4 * (Real.sin a)^3   :=  by sorry
