-- Prove2me | Theorems.Thm_lean_workbook_plus_4104
-- name    : lean_workbook_plus_4104
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.143455+00:00
-- url     : https://prove2.me/theorems/90e8d03e-19e3-4893-ba2e-e590b7029111
-- statement:
--   Prove the identity: $C_{n}^{0}+C_{n}^{1}+....+C_{n}^{n}=2^n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_4104 (n : ℕ) : ∑ k in Finset.range (n+1), Nat.choose n k = 2^n   :=  by sorry
