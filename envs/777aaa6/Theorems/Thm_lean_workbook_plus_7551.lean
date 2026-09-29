-- Prove2me | Theorems.Thm_lean_workbook_plus_7551
-- name    : lean_workbook_plus_7551
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/3d9b798b-f803-49c0-8c0e-fca8209d0c0a
-- statement:
--   Derive the identity \(\sin(x)^4+\cos(x)^4=2\, \left( \cos \left( x \right) \right) ^{4}+1-2\, \left( \cos \left( x \right) \right) ^{2}\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_7551 (x : ℝ) : (sin x)^4 + (cos x)^4 = 2 * (cos x)^4 + 1 - 2 * (cos x)^2   :=  by sorry
