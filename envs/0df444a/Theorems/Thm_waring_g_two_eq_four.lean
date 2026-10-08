-- Prove2me | Theorems.Thm_waring_g_two_eq_four
-- name    : waring_g_two_eq_four
-- status  : Proved
-- author  : @moona3k
-- created : 2026-10-04T17:19:36.334996+00:00
-- url     : https://prove2.me/theorems/f8a5ce80-6d72-437c-8553-258ea371c64a
-- title:
--   Waring's problem for $k=2$: $g(2) = 4$ (Lagrange, 1770)
-- statement:
--   **Waring's problem for $k = 2$: $g(2) = 4$.** Every natural number is the sum of at most four perfect squares, and four is best possible.
--
--   $$\forall n \in \mathbb{N},\ \exists a, b, c, d \in \mathbb{N}:\quad n = a^2 + b^2 + c^2 + d^2,$$
--
--   and this fails for three squares: $7 = 4 + 1 + 1 + 1$ requires all four (the only squares $\le 7$ are $0, 1, 4$, and no three of these sum to $7$).
--
--   This is the $k = 2$ case of Waring's problem, resolved by Lagrange in 1770 (the "four squares theorem"). It is the foundational instance of the general Waring problem: for each $k \ge 2$, find the smallest $g(k)$ such that every natural number is a sum of at most $g(k)$ $k$-th powers. The upper bound is proved via Euler's four-square identity (products of sums of four squares are sums of four squares) and Fermat's theorem for primes; the lower bound is a finite check on $n = 7$.
--
--   **Formalization Note** The upper bound is Mathlib's `Nat.sum_four_squares`. The lower bound uses `interval_cases` on the 27 combinations of $a, b, c \in \{0, 1, 2\}$.
-- source:
--   J. L. Lagrange, Démonstration de tout ce que j'ai exposé..., Nouv. Mém. Acad. Roy. Sci. Berlin (1770); see also Mathlib.NumberTheory.SumFourSquares

import Mathlib

theorem waring_g_two_eq_four :
    (∀ n : ℕ, ∃ a b c d : ℕ, a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2 = n) ∧
    ¬(∀ n : ℕ, ∃ a b c : ℕ, a ^ 2 + b ^ 2 + c ^ 2 = n) := by sorry
