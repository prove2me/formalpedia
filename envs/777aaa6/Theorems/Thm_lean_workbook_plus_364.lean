-- Prove2me | Theorems.Thm_lean_workbook_plus_364
-- name    : lean_workbook_plus_364
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/ee3800d2-cb43-414a-8556-5ee735742253
-- statement:
--   What is the smallest positive integer that leaves a remainder of $9$ when divided by $10$ , a remainder of $8$ when divided by $9$ , and so on, down to where it leaves a remainder of $1$ when divided by $2$ ?
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_364 (n : ℕ) (hA: A = ({0,1,2,3,4,5,6,7,8,9} : Finset ℕ)) (hn: n ∈ A) : ∃ m, m % 10 = 9 ∧ m % 9 = 8 ∧ m % 8 = 7 ∧ m % 7 = 6 ∧ m % 6 = 5 ∧ m % 5 = 4 ∧ m % 4 = 3 ∧ m % 3 = 2 ∧ m % 2 = 1   :=  by sorry
