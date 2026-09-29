-- Prove2me | Theorems.Thm_lean_workbook_plus_62529
-- name    : lean_workbook_plus_62529
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/09552bb5-14e6-48e2-af76-59cae7ac65bb
-- statement:
--   Find all functions $ f: R\rightarrow R$ ,that satisfy to the following condition: For all $ x,y\in R$ : $ (x+y)(f(x)-f(y))=(x-y)(f(x)+f(y))$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62529 (f : ℝ → ℝ):(∀ x y,(x+y)*(f x - f y) = (x-y)*(f x + f y)) ↔ ∃ c:ℝ,∀ x:ℝ,f x = c * x   :=  by sorry
