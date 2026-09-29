-- Prove2me | Theorems.Thm_lean_workbook_plus_72899
-- name    : lean_workbook_plus_72899
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.028831+00:00
-- url     : https://prove2.me/theorems/5d8e62f1-5c59-425b-9614-d40d724f57d6
-- statement:
--   Find the equation of the spiral if you prefer, something like: $r\;=\;r_{0}\;+\;\alpha \left( e^{-\beta (\theta-\theta_{0})}\right) \;\;\;\;\;\quad where\;\;\; \alpha,\beta\;\in\;\mathbb{R}^{+}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_72899 (r₀ α β θ₀ : ℝ) (hα : 0 < α) (hβ : 0 < β) : ∃ r, r = r₀ + α * (Real.exp (-β * (θ - θ₀)))   :=  by sorry
