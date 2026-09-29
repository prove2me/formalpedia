-- Prove2me | Theorems.Thm_lean_workbook_plus_42159
-- name    : lean_workbook_plus_42159
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.715658+00:00
-- url     : https://prove2.me/theorems/1c45e632-87f6-4804-8bf2-6b0f3be972ba
-- statement:
--   Of course, the solution can be based on more general principles starting with this lemma: Lemma: Let $ P(x)$ be a polynomial with integer coefficients. Then for any two integers $ a, b$ we have $ a-b | P(a)-P(b)$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_42159 (P : Polynomial ℤ) (a b : ℤ) : a - b ∣ P.eval a - P.eval b   :=  by sorry
