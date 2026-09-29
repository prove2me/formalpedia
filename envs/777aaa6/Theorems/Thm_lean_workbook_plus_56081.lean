-- Prove2me | Theorems.Thm_lean_workbook_plus_56081
-- name    : lean_workbook_plus_56081
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/0965b1d2-3613-4ddf-9e2e-f0bcf611cae2
-- statement:
--   Prove $\frac{1}{\left(2-\cos x\right)\left(3-\cos x\right)}=\frac{1}{2-\cos x}-\frac{1}{3-\cos x}$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56081 (x : ℝ) : (1 : ℝ) / ((2 - Real.cos x) * (3 - Real.cos x)) = 1 / (2 - Real.cos x) - 1 / (3 - Real.cos x)   :=  by sorry
