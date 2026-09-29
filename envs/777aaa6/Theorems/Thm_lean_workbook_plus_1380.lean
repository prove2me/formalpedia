-- Prove2me | Theorems.Thm_lean_workbook_plus_1380
-- name    : lean_workbook_plus_1380
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/48277d7c-9aeb-489e-9578-2369bb8242c1
-- statement:
--   Derive the identity $2(\sin{150}-\sin{80})=1-2\sin{80}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1380 (x : ℝ) : 2 * (Real.sin (150 * π / 180) - Real.sin (80 * π / 180)) = 1 - 2 * Real.sin (80 * π / 180)   :=  by sorry
