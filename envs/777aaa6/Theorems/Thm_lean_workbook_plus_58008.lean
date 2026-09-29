-- Prove2me | Theorems.Thm_lean_workbook_plus_58008
-- name    : lean_workbook_plus_58008
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:57.496679+00:00
-- url     : https://prove2.me/theorems/3e83e622-e734-4e9f-a16d-fdfaae36a6e3
-- statement:
--   Prove that there exists a number $t$ such that $t, t+n_i$ $(i \in (1, 2, ..., r))$ are not divisible by $p_i$ for all $i \in (1, 2, ..., k)$ given a set of finite primes $P = (p_1, p_2, ..., p_k)$ and numbers $n_1, n_2, ..., n_r$ which are not divisible by any $p_i \in P$.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_58008 (P : Finset ℕ) (n : ℕ → ℕ) (hP : ∀ p ∈ P, p.Prime) (hn : ∀ r, ¬ ∃ p ∈ P, p ∣ n r) : ∃ t, ∀ p ∈ P, ¬ p ∣ t + n 0   :=  by sorry
