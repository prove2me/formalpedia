-- Prove2me | Theorems.Thm_lean_workbook_plus_2806
-- name    : lean_workbook_plus_2806
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/eef44e5a-4544-4e48-9756-2aee86fa7c67
-- statement:
--   It's nice to remember that in general, the sum of the coefficients of polynomial $p(x_1,x_2,x_3,\cdots,x_n)$ is just $p(1,1,1,\cdots,1)$ (substitute 1 for all the variables)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2806 (n : ℕ) (p : Polynomial (Fin n → ℤ)) : ∑ v in p.support, p.coeff v = p.eval (1 : Fin n → ℤ)   :=  by sorry
