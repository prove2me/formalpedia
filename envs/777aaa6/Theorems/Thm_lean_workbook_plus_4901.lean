-- Prove2me | Theorems.Thm_lean_workbook_plus_4901
-- name    : lean_workbook_plus_4901
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/f4cf4ecc-229c-49ff-8904-de5832f13f3c
-- statement:
--   Consider the quadratic $x^2 - (4m + 1)x + 4m^2.$ If its roots are $r$ and $s,$ then $r + s = 4m + 1$ and $rs = 4m^2$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4901  (m r s : ℂ)
  (f : ℂ → ℂ)
  (h₀ : ∀ x, f x = x^2 - (4 * m + 1) * x + 4 * m^2)
  (h₁ : f r = 0)
  (h₂ : f s = 0)
  (h₃ : r ≠ s) :
  r + s = 4 * m + 1 ∧ r * s = 4 * m^2   :=  by sorry
