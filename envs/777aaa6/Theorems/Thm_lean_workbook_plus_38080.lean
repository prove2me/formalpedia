-- Prove2me | Theorems.Thm_lean_workbook_plus_38080
-- name    : lean_workbook_plus_38080
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/57b59be9-72f7-4ae6-8c9c-45919b299c8d
-- statement:
--   Solving for $c$ from LHS and RHS of $(1)$ and $(2)$ we get: \n\n \begin{eqnarray*}(1)\wedge (2) &\Longleftrightarrow & 5k\le c\le 6k\,\wedge\, 6k-10\le c\le 5k+7\&\Longleftrightarrow &\max\{5k,6k-10\}\le c\le\min\{6k,5k+7\}\end{eqnarray*} \n\n
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_38080  (k c : ℝ)
  (h₀ : 5 * k ≤ c)
  (h₁ : c ≤ 6 * k)
  (h₂ : 6 * k - 10 ≤ c)
  (h₃ : c ≤ 5 * k + 7) :
  max (5 * k) (6 * k - 10) ≤ c ∧ c ≤ min (6 * k) (5 * k + 7)   :=  by sorry
