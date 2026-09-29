-- Prove2me | Theorems.Thm_lean_workbook_plus_28301
-- name    : lean_workbook_plus_28301
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/b41a2f33-6bd1-4b9d-8c81-e4ce41d6f657
-- statement:
--   Lemma. For any $\theta$ , $\cos\left(\theta\right)+\cos\left(\theta+\frac{2\pi}{3}\right)+\cos\left(\theta+\frac{4\pi}{3}\right)=0$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_28301 (θ : ℝ) : Real.cos θ + Real.cos (θ + (2 * Real.pi / 3)) + Real.cos (θ + (4 * Real.pi / 3)) = 0   :=  by sorry
