-- Prove2me | Theorems.Thm_lean_workbook_plus_59500
-- name    : lean_workbook_plus_59500
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/6fe44b51-3d10-44d5-a184-99f8c9733bee
-- statement:
--   we have $x+y=5-z, $ & $x^2+y^2=19-z^2$ .\nform cauchy S\n\n $(x+y)^2\leq{2(x^2+y^2)}$\n\n $\implies{(5-z)^2\leq{2(19-z^2)}}$\n\n $\implies{-1\leq{z}\leq{\frac{13}{3}}}$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_59500  (x y z : ℝ)
  (h₀ : x + y = 5 - z)
  (h₁ : x^2 + y^2 = 19 - z^2) :
  -1 ≤ z ∧ z ≤ 13/3   :=  by sorry
