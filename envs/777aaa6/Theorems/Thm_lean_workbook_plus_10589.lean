-- Prove2me | Theorems.Thm_lean_workbook_plus_10589
-- name    : lean_workbook_plus_10589
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/547518f8-99fa-43c5-a89b-d92ffc120057
-- statement:
--   Find all continuous functions $f:[0;1]\to\mathbb{R}$ such that $f(x^2)+f(x)=x,\forall x\in [0;1]$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_10589 (f : ℝ → ℝ) (hf: ContinuousOn f (Set.Icc 0 1)) (hx: ∀ x ∈ (Set.Icc 0 1), f (x^2) + f x = x) : ∀ x ∈ (Set.Icc 0 1), f x = x - x^2   :=  by sorry
