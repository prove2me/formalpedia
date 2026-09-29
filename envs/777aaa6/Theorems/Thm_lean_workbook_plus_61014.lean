-- Prove2me | Theorems.Thm_lean_workbook_plus_61014
-- name    : lean_workbook_plus_61014
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/4ff85803-f8d5-4ac3-9508-6ba300863f73
-- statement:
--   Find the range of $\sec^2{\theta}+\csc^2{\theta}$ for real angles $\theta$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_61014 (f : ℝ → ℝ) (fvalue: ∀ θ : ℝ, f θ = (1 / Real.cos θ) ^ 2 + (1 / Real.sin θ) ^ 2) : Set.range f = Set.Ici 4   :=  by sorry
