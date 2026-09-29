-- Prove2me | Theorems.Thm_lean_workbook_plus_16473
-- name    : lean_workbook_plus_16473
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.685829+00:00
-- url     : https://prove2.me/theorems/552cf522-9ae5-4dd0-87dc-d8f26108177f
-- statement:
--   Suppose that $n$ is a natural number NOT divisible by $2,5$ .Prove that there is a multiple of $n$ having all digits equal to 1.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_16473 (n : ℕ) (hn2 : ¬ n % 2 = 0) (hn5 : ¬ n % 5 = 0) : ∃ m : ℕ, (m % n = 0 ∧ ∀ i ∈ Nat.digits 10 m, i = 1)   :=  by sorry
