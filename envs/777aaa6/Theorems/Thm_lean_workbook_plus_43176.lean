-- Prove2me | Theorems.Thm_lean_workbook_plus_43176
-- name    : lean_workbook_plus_43176
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.862991+00:00
-- url     : https://prove2.me/theorems/31c8b9e4-0023-4969-b7c4-94e79a6bfc95
-- statement:
--   If $m\in[-1,1]$ then put $m=sin(\theta)$ where $\theta\in[-\pi/2,\pi/2]$ . Thus $cos(\theta)\geq{0}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_43176 : ∀ m : ℝ, m ∈ Set.Icc (-1) 1 → ∃ θ : ℝ, θ ∈ Set.Icc (-Real.pi/2) (Real.pi/2) ∧ m = Real.sin θ   :=  by sorry
