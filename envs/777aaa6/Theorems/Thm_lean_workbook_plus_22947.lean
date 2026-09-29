-- Prove2me | Theorems.Thm_lean_workbook_plus_22947
-- name    : lean_workbook_plus_22947
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/1084966c-0f15-40d7-af8a-18f85ad88603
-- statement:
--   Case 1 : If $a=c=0$ set of solutions is $\mathbb R$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_22947 (a b c : ℝ) (h₁ : a = 0) (h₂ : c = 0) : Set.univ = {x : ℝ | x^2 + b * x + 0 = 0}   :=  by sorry
