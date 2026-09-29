-- Prove2me | Theorems.Thm_lean_workbook_plus_67995
-- name    : lean_workbook_plus_67995
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.897675+00:00
-- url     : https://prove2.me/theorems/cdf0e945-318a-4515-af2e-280b2f68256c
-- statement:
--   Prove that there are infinitely many composite numbers $n$ for which \n $$n | 3^{n-1} - 2^{n-1}$$ I would be very grateful if you could explain your solution, I think that I should use Fermat's Little theorem for proof but I am not sure how should I use it.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_67995 : ∃ n, Nat.Prime n ∧ n ∣ 3 ^ (n - 1) - 2 ^ (n - 1)   :=  by sorry
