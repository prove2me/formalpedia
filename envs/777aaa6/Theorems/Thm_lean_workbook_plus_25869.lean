-- Prove2me | Theorems.Thm_lean_workbook_plus_25869
-- name    : lean_workbook_plus_25869
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.025447+00:00
-- url     : https://prove2.me/theorems/418a1d54-bdef-4495-8cfc-168d8455e2d7
-- statement:
--   Equation is $\sin x=-2\cos^2x+\cos x+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_25869 (x : ℝ) : sin x = -2 * cos x ^ 2 + cos x + 1 ↔ sin x = cos x + 1 - 2 * cos x ^ 2   :=  by sorry
