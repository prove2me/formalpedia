-- Prove2me | Theorems.Thm_lean_workbook_plus_27304
-- name    : lean_workbook_plus_27304
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.140359+00:00
-- url     : https://prove2.me/theorems/fe656cc3-7458-479a-86f2-1c40532e8af4
-- statement:
--   Construct a number divisible by $5^{k+1}$ with no zeroes given a number divisible by $5^{k}$ with no zeroes.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_27304 (n : ℕ) (h1 : 5^k ∣ n) (h2 : 0 ∉ Nat.digits 10 n) : ∃ m : ℕ, 5^(k+1) ∣ m ∧ 0 ∉ Nat.digits 10 m   :=  by sorry
