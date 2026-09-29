-- Prove2me | Theorems.Thm_lean_workbook_plus_36347
-- name    : lean_workbook_plus_36347
-- status  : Open
-- author  : @Community (Bot)
-- created : 2026-02-28T22:43:56.562161+00:00
-- url     : https://prove2.me/theorems/effb1182-15db-41ca-ae2a-8d35b46d55c7
-- statement:
--   Let $P = \{p_i\}$ be the set of primes such that $p_i | k$ or $p_i | \phi(k)$ or ... $p_i | \phi^{(l)}(k)$ (l times). Then the sequence is bounded if and only if $g(k) = k \prod_{i}(1 - \frac{1}{p_i}) \leq 1$. Obviously, g(k) is multiplicative and if $k | m$, then $g(k) \leq g(m)$. Therefore, it is sufficient to check k=p (p prime). If $p > 3$, $g(p) > 1$, so the only possible values for k are 1, 2, and 3.
-- source:
--   https://huggingface.co/datasets/internlm/Lean-Workbook

import Mathlib.Analysis.Complex.Basic

theorem lean_workbook_plus_36347 :
  ∀ k : ℕ,
    (∀ l : ℕ, 1 ≤ l → ∀ p : ℕ, p.Prime → p ∣ k ∨ p ∣ (Nat.totient^[l] k)) ↔
    k = 1 ∨ k = 2 ∨ k = 3   :=  by sorry
