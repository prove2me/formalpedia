-- Prove2me | Theorems.Thm_lean_workbook_plus_36698
-- name    : lean_workbook_plus_36698
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/9a9f5585-c1c5-4878-8b44-fff89fc2be2a
-- statement:
--   Since n has exactly 8 natural divisors, $n$ is one of the forms $p^7, pq^3, pqr$ where $p,q,r$ are some primes.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36698 (n : ℕ) (hn : n > 0) (h : Finset.card (Nat.divisors n) = 8) : ∃ (p q r : ℕ), p.Prime ∧ q.Prime ∧ r.Prime ∧ n = p^7 ∨ n = p*q^3 ∨ n = p*q*r   :=  by sorry
