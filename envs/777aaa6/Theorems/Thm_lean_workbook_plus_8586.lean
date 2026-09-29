-- Prove2me | Theorems.Thm_lean_workbook_plus_8586
-- name    : lean_workbook_plus_8586
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.293252+00:00
-- url     : https://prove2.me/theorems/28d56b88-bac7-4d57-8381-8e574c2805ee
-- statement:
--   Prove that every natural number which is relatively prime with $2$ and $5$ admits a multiple with all digits equal to $7$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_8586 (n : ℕ) (hn : Nat.Coprime n 2) (hn' : Nat.Coprime n 5) : ∃ m : ℕ, (m % n = 0 ∧ ∀ k ∈ Nat.digits 10 m, k = 7)   :=  by sorry
