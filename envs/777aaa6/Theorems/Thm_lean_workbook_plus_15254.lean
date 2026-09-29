-- Prove2me | Theorems.Thm_lean_workbook_plus_15254
-- name    : lean_workbook_plus_15254
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/e876fb9e-ddda-4c6b-b0a0-e3030ddab3a4
-- statement:
--   Prove that $ 1 + \cos x = 2\cos^2 \frac {x}{2}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_15254 : 1 + Real.cos x = 2 * (Real.cos (x / 2)) ^ 2   :=  by sorry
