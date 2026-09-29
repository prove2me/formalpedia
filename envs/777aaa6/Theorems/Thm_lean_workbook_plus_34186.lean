-- Prove2me | Theorems.Thm_lean_workbook_plus_34186
-- name    : lean_workbook_plus_34186
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/918dd0e9-c4a1-42b1-9f1b-83a7e84c1caf
-- statement:
--   Prove that $\sin{3x}=3\sin{x}-4\sin^3{x}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34186 (x : ℝ) : Real.sin (3 * x) = 3 * Real.sin x - 4 * (Real.sin x)^3   :=  by sorry
