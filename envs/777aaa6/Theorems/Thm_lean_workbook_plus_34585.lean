-- Prove2me | Theorems.Thm_lean_workbook_plus_34585
-- name    : lean_workbook_plus_34585
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.431937+00:00
-- url     : https://prove2.me/theorems/c1156290-7612-4460-a039-cb8199537f5b
-- statement:
--   Prove the identity \(\sum_{k=0}^m(-1)^k\binom{2n+1}{k}=(-1)^m\binom{2n}{m}\) using induction over \(m\).
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_34585 (n m : ℕ) : ∑ k in Finset.range (m+1), (-1 : ℤ)^k * (2*n+1).choose k = (-1)^m * (2*n).choose m   :=  by sorry
