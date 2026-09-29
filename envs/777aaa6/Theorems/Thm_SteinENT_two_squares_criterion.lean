-- Prove2me | Theorems.Thm_SteinENT_two_squares_criterion
-- name    : SteinENT.two_squares_criterion
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:24:24.038594+00:00
-- url     : https://prove2.me/theorems/dc497b2c-3d8e-4437-a791-2198c5a8fbd9
-- title:
--   Theorem 5.7.1 — The prime-factor criterion for two integer squares
-- statement:
--   Let $n$ be a positive integer. For a prime $p$, let $v_p(n)$ denote its exponent in the prime factorization of $n$. Then
--
--   $$n=x^2+y^2\text{ for some }x,y\in\mathbb Z\quad\Longleftrightarrow\quad v_p(n)\text{ is even for every prime }p\mid n\text{ with }p\equiv3\pmod4.$$
--
--   This gives a complete arithmetic criterion for representability, including composite integers.
--
--   **Formalization Note** The input and primes are natural numbers, with positivity explicit. Square coordinates are integers, and `Nat.factorization` records the prime exponent.
-- source:
--   William Stein, Elementary Number Theory: Primes, Congruences, and Secrets, author-hosted 2017 PDF, Theorem 5.7.1, printed pp. 117–120. https://wstein.org/ent/ent.pdf ; pinned author TeX commit c4984c7ddb22258674816f8c000b0d8eb485d694, body.tex lines 6883–6887;6957–7042: https://github.com/williamstein/ent/blob/c4984c7ddb22258674816f8c000b0d8eb485d694/body.tex

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace SteinENT
theorem two_squares_criterion (n : ℕ) (hn : 0 < n) :
    (∃ x y : ℤ, (n : ℤ) = x ^ 2 + y ^ 2) ↔
      ∀ p : ℕ, p.Prime → p ∣ n → p % 4 = 3 → Even (n.factorization p) := by sorry
end SteinENT
