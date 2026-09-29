-- Prove2me | Theorems.Thm_lean_workbook_plus_8403
-- name    : lean_workbook_plus_8403
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/5ccb69df-60e4-4ce8-ac85-3cd9f02805f8
-- statement:
--   Find the range of $p$ given $\sin p \in \left[-1,\frac{1-\sqrt{5}}{4}\right]U\left[\frac{1+\sqrt{5}}{4},1\right]$ and $-\frac{\pi}{2} \leq p \leq \frac{\pi}{2}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8403 (p : ℝ) (hp₁ : -π/2 ≤ p ∧ p ≤ π/2) (hp₂ : -1 ≤ sin p ∧ sin p ≤ (1 - Real.sqrt 5)/4 ∨ (1 + Real.sqrt 5)/4 ≤ sin p ∧ sin p ≤ 1) : p ∈ Set.Icc (-π/2) (π/2)   :=  by sorry
