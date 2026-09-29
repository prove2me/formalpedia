-- Prove2me | Theorems.Thm_lean_workbook_plus_1003
-- name    : lean_workbook_plus_1003
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/d8aab7d5-45c2-43b1-bf91-64998f849218
-- statement:
--   SolutionIdeally, $abc-def=1$ . Guessing and checking without using $9$ or $8$ in the numerator gives $\\frac{6\cdot3\cdot2-7\cdot5\cdot1}{9\cdot8\cdot4}$ . Since $abc-def=1$ , then one of $\{a,b,c\}$ or $\{d,e,f\}$ must contain only odd factors, and trying the $1,3,5$ case means one of them must be $7$ or $9$ . As well, it's impossible to get $\\frac{1}{9\cdot8\cdot6}$ by checking all of the cases, leaving $\\frac{6\cdot3\cdot2-7\cdot5\cdot1}{9\cdot8\cdot4}=\frac{1}{288}$ as the minimum positive fraction achievable, for an answer of $\boxed{289}$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_1003  (a b c d e f : ℕ)
  (h₀ : 0 < a ∧ 0 < b ∧ 0 < c ∧ 0 < d ∧ 0 < e ∧ 0 < f)
  (h₁ : a * b * c - d * e * f = 1) :
  (a * b * c - d * e * f : ℚ) ≥ 1 / 288   :=  by sorry
