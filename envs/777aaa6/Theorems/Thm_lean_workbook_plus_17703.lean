-- Prove2me | Theorems.Thm_lean_workbook_plus_17703
-- name    : lean_workbook_plus_17703
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/d7b81cd0-346e-4779-8ed9-01a561456d8e
-- statement:
--   Denote t=xy. Now $a^3=(x+y)^3=x^3+y^3+3xy(x+y)=x^3+y^3+3at\implies x^3+y^3=a^3-3at$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_17703  (x y a t : ℝ)
  (h₀ : t = x * y)
  (h₁ : a = x + y) :
  x^3 + y^3 = a^3 - 3 * a * t   :=  by sorry
