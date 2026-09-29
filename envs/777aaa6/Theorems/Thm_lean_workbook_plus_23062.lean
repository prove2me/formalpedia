-- Prove2me | Theorems.Thm_lean_workbook_plus_23062
-- name    : lean_workbook_plus_23062
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.916039+00:00
-- url     : https://prove2.me/theorems/5c817d40-01d5-4be0-8205-fc505e76ddf2
-- statement:
--   Let $y=x-\frac 12$ and the equation is $\lfloor y+1\rfloor+\lfloor y\rfloor=\lfloor 2y+1\rfloor$ $\iff$ $2\lfloor y\rfloor=\lfloor 2y\rfloor$ $\iff$ $y\in[n,n+\frac 12)$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_23062  (y : ℝ)
  (n : ℤ)
  (h₀ : n ≤ y)
  (h₁ : y < n + 1 / 2) :
  Int.floor (y + 1) + Int.floor y = Int.floor (2 * y + 1)   :=  by sorry
