-- Prove2me | Theorems.Thm_lean_workbook_plus_1672
-- name    : lean_workbook_plus_1672
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/e19062b1-729f-4da5-b62a-13fe52ca57db
-- statement:
--   Prove that $\cos(\dfrac{\pi}{2} + \theta ) = - \sin\theta$ , using the unit circle.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1672 (θ : ℝ) : Real.cos (Real.pi / 2 + θ) = - Real.sin θ   :=  by sorry
