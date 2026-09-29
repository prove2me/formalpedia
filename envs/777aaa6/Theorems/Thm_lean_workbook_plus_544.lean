-- Prove2me | Theorems.Thm_lean_workbook_plus_544
-- name    : lean_workbook_plus_544
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/f0c9a02b-ce06-47b0-90d0-8517e74b7e6c
-- statement:
--   $P(x,x)$ $\implies$ $f(x)^2=1$ and so $f(x)\in\{-1,1\}$ $\forall x$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_544 (f : ℝ → ℝ) (h : ∀ x, f x ^ 2 = 1) : Set.range f ⊆ {1, -1}   :=  by sorry
