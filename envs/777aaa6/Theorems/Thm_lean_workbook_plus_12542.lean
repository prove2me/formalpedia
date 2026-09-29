-- Prove2me | Theorems.Thm_lean_workbook_plus_12542
-- name    : lean_workbook_plus_12542
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/b017fc35-9fc8-4bff-ba6d-bdad1e5bb6d8
-- statement:
--   The inequality simplifies further to $(1-\cos\theta)(r_1-r_2)^2 \geq 0$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_12542 (r₁ r₂ : ℝ) (θ : ℝ) : (1 - Real.cos θ) * (r₁ - r₂) ^ 2 ≥ 0   :=  by sorry
