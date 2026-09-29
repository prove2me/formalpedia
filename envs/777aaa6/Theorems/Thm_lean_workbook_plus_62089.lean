-- Prove2me | Theorems.Thm_lean_workbook_plus_62089
-- name    : lean_workbook_plus_62089
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.629978+00:00
-- url     : https://prove2.me/theorems/272986bd-540c-4b7c-934b-aff62a2205fd
-- statement:
--   Given the Wilson's theorem: $(p-1)! \equiv -1 \mod p$ for a prime $p > 2$, prove that if $n$ divides $(n-2)!$ and $n > 3$, then $n$ is not prime, and classify the possible forms of $n$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_62089 {n : ℕ} (hn : 3 < n) (h : n ∣ (n-2)!): ¬ Nat.Prime n   :=  by sorry
