-- Prove2me | Theorems.Thm_lean_workbook_plus_74641
-- name    : lean_workbook_plus_74641
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/5f101992-0522-421b-9ce2-c19ebb218bd0
-- statement:
--   Find all continuous function $ f;R \to R$ such that $ f( \alpha x+ \beta y) = \alpha f(x) + \beta f(y), \forall x,y, \in R$ given $ \alpha + \beta = 1$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74641 (α β : ℝ) (h : α + β = 1) : ∃ f : ℝ → ℝ, Continuous f ∧ ∀ x y : ℝ, f (α * x + β * y) = α * f x + β * f y   :=  by sorry
