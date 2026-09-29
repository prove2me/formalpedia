-- Prove2me | Theorems.Thm_lean_workbook_plus_39381
-- name    : lean_workbook_plus_39381
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/849f2ed5-41f7-4c73-bdef-011e1d2dca14
-- statement:
--   Define $r_1, r_2$ to be the roots of the first equation, similarly for $r_3, r_4, r_5, r_6.$\n\n$r_1+r_2=a, r_1r_2=b$\n$r_3+r_4=b, r_3r_4=c$\n$r_5+r_6=c, r_5r_6=a$\nWe take advantage of the symmetry by adding each equation to get\n$r_1+r_2+r_3+r_4+r_5+r_6=r_1r_2+r_3r_4+r_5r_6.$\nSince we're only looking for integers, we factor as:\n\n$(r_1-1)(r_2-1)+(r_3-1)(r_4-1)+(r_5-1)(r_6-1)=3$.\n\nNow there're only so many ways this is true. More, because $a, b, c$ are all positive, $r_i > 0.$ I'll leave you to find all the possibilities (and permutations).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_39381  (a b c r₁ r₂ r₃ r₄ r₅ r₆ : ℤ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c)
  (h₁ : r₁ + r₂ = a)
  (h₂ : r₁ * r₂ = b)
  (h₃ : r₃ + r₄ = b)
  (h₄ : r₃ * r₄ = c)
  (h₅ : r₅ + r₆ = c)
  (h₆ : r₅ * r₆ = a)
  : (r₁ - 1) * (r₂ - 1) + (r₃ - 1) * (r₄ - 1) + (r₅ - 1) * (r₆ - 1) = 3   :=  by sorry
