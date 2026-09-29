-- Prove2me | Theorems.Thm_lean_workbook_plus_13286
-- name    : lean_workbook_plus_13286
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.554211+00:00
-- url     : https://prove2.me/theorems/db975d86-4cec-42e0-8dad-be6e8f1b6b0c
-- statement:
--   Prove $\sum_{k=0}^n \dbinom{n}{k}=2^n$
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_13286 (n : ℕ) : ∑ k in (Finset.range (n+1)), (Nat.choose n k) = 2^n   :=  by sorry
