-- Prove2me | Theorems.Thm_lean_workbook_plus_40093
-- name    : lean_workbook_plus_40093
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/d40d98e8-590b-452d-8063-de8124f13735
-- statement:
--   Let $a=\cos^2\alpha$ , $b=\cos^2\beta$ and $c=\cos^2\gamma,$ where $\{\alpha,\beta,\gamma\}\subset\left[0,\frac{\pi}{2}\right]$ .\n\nThus, we need to prove that:\n $$-\cos(\alpha+\beta+\gamma)\leq1.$$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_40093 (α β γ : ℝ) (hα : α ∈ Set.Icc 0 (Real.pi / 2)) (hβ : β ∈ Set.Icc 0 (Real.pi / 2)) (hγ : γ ∈ Set.Icc 0 (Real.pi / 2)) : -Real.cos (α + β + γ) ≤ 1   :=  by sorry
