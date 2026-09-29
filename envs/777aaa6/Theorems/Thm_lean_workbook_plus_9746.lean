-- Prove2me | Theorems.Thm_lean_workbook_plus_9746
-- name    : lean_workbook_plus_9746
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/825c36a8-8626-45e2-8ab1-56424e05c7b2
-- statement:
--   Prove $ \sum_{k=0}^n3^kC^n_k=4^n$ .
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9746 (n:ℕ) : ∑ k in Finset.range (n+1), (3^k* Nat.choose n k) = 4^n   :=  by sorry
