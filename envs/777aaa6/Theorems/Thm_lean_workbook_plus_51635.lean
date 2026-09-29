-- Prove2me | Theorems.Thm_lean_workbook_plus_51635
-- name    : lean_workbook_plus_51635
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.231389+00:00
-- url     : https://prove2.me/theorems/2b33ed71-5216-42fc-a942-482191cdf7c8
-- statement:
--   For $\boxed{\Leftarrow}$ we have $b=ac,$ so $x^b-1=(x^a)^c-1=(x^a-1)((x^a)^{c-1}+(x^a)^{c-2}+\ldots+x^a+1)$ is divisible by $x^a-1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_51635  (x a b : ℕ)
  (h₀ : 1 < a ∧ 1 < b)
  (h₁ : b = a * c)
  (h₂ : 0 < c) :
  (x^b - 1) % (x^a - 1) = 0   :=  by sorry
