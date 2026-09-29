-- Prove2me | Theorems.Thm_lean_workbook_plus_11215
-- name    : lean_workbook_plus_11215
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/aa330e17-9bf4-4ae0-a35a-c7c7dbc46574
-- statement:
--   prove that : \n$ 3(\cos^2x+\cos^2y+\cos^2z) \geq ( \cos x+ \cos y+ \cos z)^2$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_11215 (x y z: ℝ) : 3 * (Real.cos x ^ 2 + Real.cos y ^ 2 + Real.cos z ^ 2) ≥ (Real.cos x + Real.cos y + Real.cos z) ^ 2   :=  by sorry
