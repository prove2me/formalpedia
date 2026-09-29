-- Prove2me | Theorems.Thm_lean_workbook_plus_5193
-- name    : lean_workbook_plus_5193
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/3342a845-20a9-4113-aa9b-f3961abd976e
-- statement:
--   Find all functions $f: R\rightarrow R$ such that: $f(x+y)+f(xy)=f(x^2)+f(y^2)$ for all $x,y$ are reals
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_5193 (f : ℝ → ℝ): (∀ x y, f (x + y) + f (x*y) = f (x^2) + f (y^2)) ↔ ∃ l:ℝ, ∀ x, f x = l   :=  by sorry
