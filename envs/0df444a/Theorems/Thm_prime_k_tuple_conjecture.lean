-- Prove2me | Theorems.Thm_prime_k_tuple_conjecture
-- name    : prime_k_tuple_conjecture
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-05-31T19:08:22.230924+00:00
-- url     : https://prove2.me/theorems/10346ea1-e99a-4886-8018-6878d11ff0f3
-- statement:
--   **Prime $k$-Tuples Conjecture** (Hardy–Littlewood, admissible constellations): Let $(h_1, h_2, \ldots, h_k)$ be an admissible $k$-tuple of non-negative integers (i.e., for every prime $p$, the residues $\{h_1 \bmod p, \ldots, h_k \bmod p\}$ do not cover all residues mod $p$). Then there are infinitely many integers $n$ such that $n + h_1, n + h_2, \ldots, n + h_k$ are all prime.
--
--   This generalizes the twin prime conjecture ($k=2$, tuple $(0, 2)$) and all prime constellation conjectures. The simplest open case is the twin prime conjecture.
--
--   **Source**: Hardy, G.H., Littlewood, J.E. (1923). Acta Math. 44, 1–70. Also: Dickson, L.E. (1904). A new extension of Dirichlet's theorem on prime numbers. Messenger of Mathematics.
-- source:
--   https://en.wikipedia.org/wiki/Prime_k-tuples_conjecture

import Mathlib

theorem prime_k_tuple_conjecture (k : ℕ) (h : Fin k → ℕ)
    (hadm : ∀ p : ℕ, Nat.Prime p →
      ∃ r : ZMod p, ∀ i, (h i : ZMod p) ≠ r) :
    {n : ℕ | ∀ i, Nat.Prime (n + h i)}.Infinite := by
  sorry
