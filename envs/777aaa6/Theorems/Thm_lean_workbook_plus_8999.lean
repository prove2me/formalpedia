-- Prove2me | Theorems.Thm_lean_workbook_plus_8999
-- name    : lean_workbook_plus_8999
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/dca9c692-867c-443c-98da-b834282e2bd0
-- statement:
--   Let $ m$ be a positive odd integer, $ m > 2.$ Find the smallest positive integer $ n$ such that $ 2^{1989}$ divides $ m^n - 1.$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8999 (m : ℕ) (hm1 : 2 < m) (hm2 : Odd m) : ∃ n : ℕ, (2^1989 ∣ m^n - 1) ∧ (∀ k : ℕ, (2^1989 ∣ m^k - 1) → n ≤ k)   :=  by sorry
