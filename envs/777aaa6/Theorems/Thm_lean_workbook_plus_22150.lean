-- Prove2me | Theorems.Thm_lean_workbook_plus_22150
-- name    : lean_workbook_plus_22150
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/d25b7c4b-5425-4b83-83a6-c710991d82eb
-- statement:
--   Prove that $\cos2\theta = 1 - 2\sin^2\theta$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22150 (θ : ℝ) : Real.cos (2 * θ) = 1 - 2 * (Real.sin θ)^2   :=  by sorry
