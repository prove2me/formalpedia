-- Prove2me | Theorems.Thm_lean_workbook_plus_52212
-- name    : lean_workbook_plus_52212
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/72554e9d-2ac6-44d2-83a1-60c1045a0506
-- statement:
--   For $\pi < \theta < \frac{3\pi}{2}$ , $sin(\theta) < 0$ and $cos(\theta) < 0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_52212 (θ : ℝ) (h₁ : π < θ) (h₂ : θ < 3 * π / 2) : sin θ < 0 ∧ cos θ < 0   :=  by sorry
