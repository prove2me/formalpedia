-- Prove2me | Theorems.Thm_lean_workbook_plus_47854
-- name    : lean_workbook_plus_47854
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.988191+00:00
-- url     : https://prove2.me/theorems/16148413-4a4e-4f67-88c6-65c9f2aa862b
-- statement:
--   Prove that $2(\sin^2x+\cos^2x)\ge(\sin x+\cos x)^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_47854 (x : ℝ) :
  2 * (sin x ^ 2 + cos x ^ 2) ≥ (sin x + cos x) ^ 2   :=  by sorry
