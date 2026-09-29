-- Prove2me | Theorems.Thm_lean_workbook_plus_56187
-- name    : lean_workbook_plus_56187
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.366127+00:00
-- url     : https://prove2.me/theorems/06b12556-a029-4123-9f59-0b86bdc5443d
-- statement:
--   Prove that $ \sum_{i=0}^{n}\left[\binom{n}{i}\sum_{j=0}^{i}\binom{i}{j}\right]=3^{n}\forall n\in\mathbb N$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_56187 (n : ℕ) : ∑ i in Finset.range (n+1), (Nat.choose n i * ∑ j in Finset.range (i+1), Nat.choose i j) = 3^n   :=  by sorry
