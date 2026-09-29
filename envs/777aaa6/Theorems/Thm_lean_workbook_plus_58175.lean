-- Prove2me | Theorems.Thm_lean_workbook_plus_58175
-- name    : lean_workbook_plus_58175
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/5cf3a77c-f328-4173-a966-4bd42d64576c
-- statement:
--   If events $T_1,T_2,T_3$ (the events of passing the tests in question) were independent, then: $P(T_1\cap T_2)=ab$ $P(T_1\cap T_3)=\tfrac12 a$ $P(T_1\cap T_2\cap T_3)=\tfrac12ab$ So by inclusion-exclusion, $P[(T_1\cap T_2)\cup (T_1\cap T_3)]=ab+\tfrac12a-\tfrac12ab=\frac12(a+ab).$ This - the probability of the student being successful - is given to be $\frac12.$ So $a(1+b)=1$ and that's the relationship between $a$ and $b.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58175  (a b : ℝ)
  (h₀ : 0 < a ∧ 0 < b)
  (h₁ : a * b + a / 2 - a * b / 2 = 1 / 2) :
  a * (1 + b) = 1   :=  by sorry
