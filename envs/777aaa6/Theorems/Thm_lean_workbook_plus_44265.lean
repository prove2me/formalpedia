-- Prove2me | Theorems.Thm_lean_workbook_plus_44265
-- name    : lean_workbook_plus_44265
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/dc97e9fb-b2bc-458e-a3ae-869ea5a06194
-- statement:
--   Prove the trigonometric identity $2sinxcosx=sin2x$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_44265 (x : ℝ) : 2 * Real.sin x * Real.cos x = Real.sin (2 * x)   :=  by sorry
