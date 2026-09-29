-- Prove2me | Theorems.Thm_lean_workbook_plus_9404
-- name    : lean_workbook_plus_9404
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:55.412125+00:00
-- url     : https://prove2.me/theorems/178f8ed7-27b6-4c28-8b77-a850b7ae364b
-- statement:
--   Derive the identity \( (1+1)^n=\binom{n}{0}\cdot 1+\binom{n}{1}\cdot 1 +\cdots +\binom{n}{n}\cdot 1 \) and show how it leads to \( 2^n= \binom{n}{0}+\binom{n}{1}+\cdots+\binom{n}{n} \)
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_9404 : ∀ n : ℕ, (1 + 1) ^ n = ∑ i in Finset.range n, (Nat.choose n i) * 1   :=  by sorry
