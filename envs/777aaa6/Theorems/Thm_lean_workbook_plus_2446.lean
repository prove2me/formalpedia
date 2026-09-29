-- Prove2me | Theorems.Thm_lean_workbook_plus_2446
-- name    : lean_workbook_plus_2446
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:54.833458+00:00
-- url     : https://prove2.me/theorems/a26a191a-c7f1-4112-ad44-d230c01f2f59
-- statement:
--   Prove that for every $n\in N$ there is a number with digits 1 or 2 that is divisible by $2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_2446 (n : ℕ) : ∃ m, (m % 2 ^ n = 0 ∧ (∀ i ∈ Nat.digits 10 m, i = 1 ∨ i = 2))   :=  by sorry
