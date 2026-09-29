-- Prove2me | Theorems.Thm_lean_workbook_plus_78509
-- name    : lean_workbook_plus_78509
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.289288+00:00
-- url     : https://prove2.me/theorems/4b257e65-a0a6-4731-ac91-57cc2fb8dfe2
-- statement:
--   Find all function polynome P such that : \n $\forall x \in \mathbb{R} ; P(x+1) = P(x)+2x+1$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_78509 (P : Polynomial ℝ) (hP : ∀ x : ℝ, P.eval (x + 1) = P.eval x + 2 * x + 1) :
    ∃ a : ℝ, ∀ x : ℝ, P.eval x = a * x + a   :=  by sorry
