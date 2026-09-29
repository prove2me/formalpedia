-- Prove2me | Theorems.Thm_lean_workbook_plus_52573
-- name    : lean_workbook_plus_52573
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/e2ae2ef6-ac77-4bfe-b87c-888472e1205f
-- statement:
--   If $|x|=|y|$, prove that $(x^2-y^2)^2=0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52573 (x y : ℝ) (h : abs x = abs y) : (x^2-y^2)^2 = 0   :=  by sorry
