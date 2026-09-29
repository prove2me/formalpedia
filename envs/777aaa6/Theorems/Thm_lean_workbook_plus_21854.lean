-- Prove2me | Theorems.Thm_lean_workbook_plus_21854
-- name    : lean_workbook_plus_21854
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/4ed781d1-eb8c-4d0a-ab64-204b719be3c2
-- statement:
--   Prove that there does not exist the function $f:\mathbb {R} \rightarrow \mathbb {R}$ such that $f(0)=0$ and $f(x+y) \geq f(x)+yf(f(x)), \forall x, y \in \mathbb{R}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_21854    (f : ℝ → ℝ)
    (h₀ : f 0 = 0)
    (h₁ : ∀ x y, f (x + y) ≥ f x + y * f (f x)) :
    False   :=  by sorry
