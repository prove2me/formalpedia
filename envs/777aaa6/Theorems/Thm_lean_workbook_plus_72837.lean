-- Prove2me | Theorems.Thm_lean_workbook_plus_72837
-- name    : lean_workbook_plus_72837
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/2a21674d-afc8-4285-8d3c-2396e25bd129
-- statement:
--   This is $(\sin 2x(1+2\cos x))^2+(\cos 2x(1+2\cos x))^2=1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72837 : ∀ x : ℝ, (sin 2*x*(1 + 2*cos x))^2 + (cos 2*x*(1 + 2*cos x))^2 = 1   :=  by sorry
