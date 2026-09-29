-- Prove2me | Theorems.Thm_lean_workbook_plus_74358
-- name    : lean_workbook_plus_74358
-- status  : Disproved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:58.170827+00:00
-- url     : https://prove2.me/theorems/f883e438-6828-4600-939c-a7fb61e9053b
-- statement:
--   Prove that \n\n $\sqrt {{\frac {{a}^{3}{b}^{3}}{ \left( b+c-a \right) \left( c+a-b \right) }}}+\sqrt {{\frac {{b}^{3}{c}^{3}}{ \left( c+a-b \right) \left( a+b-c \right) }}}+\sqrt {{\frac {{c}^{3}{a}^{3}}{ \left( a+b-c \right) \left( b+c-a \right) }}}\geq 2\,R\sqrt {3}s$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_74358 :
  ∀ a b c R s : ℝ, a > 0 ∧ b > 0 ∧ c > 0 ∧ R > 0 ∧ s > 0 →
  Real.sqrt ((a^3 * b^3) / (b + c - a) / (c + a - b)) +
  Real.sqrt ((b^3 * c^3) / (c + a - b) / (a + b - c)) +
  Real.sqrt ((a^3 * c^3) / (a + b - c) / (b + c - a)) ≥
  2 * R * Real.sqrt 3 * s   :=  by sorry
