-- Prove2me | Theorems.Thm_lean_workbook_plus_54215
-- name    : lean_workbook_plus_54215
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/c5c3b7c7-e0bd-4517-8a77-1816f4b3750f
-- statement:
--   Prove that $\sin 4a = 4 \sin a \cos^{3} a - 4 \cos a \sin^{3} a$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_54215 (a : ℝ) : Real.sin (4 * a) = 4 * Real.sin a * (Real.cos a)^3 - 4 * Real.cos a * (Real.sin a)^3   :=  by sorry
