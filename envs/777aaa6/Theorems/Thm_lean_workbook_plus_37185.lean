-- Prove2me | Theorems.Thm_lean_workbook_plus_37185
-- name    : lean_workbook_plus_37185
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/59330872-4cd8-4b47-8f66-d2f966b841da
-- statement:
--   We have $ \sin^{2}{x} + \sin^{2}{2x} + \sin^{2}{3x} \ + \cos^{2}{x} + \cos^{2}{2x} + \cos^{2}{3x} \ =3 $
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_37185 : ∀ x : ℝ, (Real.sin x)^2 + (Real.sin (2 * x))^2 + (Real.sin (3 * x))^2 + (Real.cos x)^2 + (Real.cos (2 * x))^2 + (Real.cos (3 * x))^2 = 3   :=  by sorry
