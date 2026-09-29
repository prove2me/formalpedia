-- Prove2me | Theorems.Thm_SteinENT_no_primitive_representation
-- name    : SteinENT.no_primitive_representation
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:23:33.378933+00:00
-- url     : https://prove2.me/theorems/e4fbb32a-712d-4c4a-9b2d-2cbc05c8ab3e
-- title:
--   Lemma 5.7.4 — A prime obstruction to primitive representations
-- statement:
--   A representation $n=x^2+y^2$ by integer coordinates is primitive when $\gcd(x,y)=1$. If a positive integer $n$ has a prime divisor $p\equiv3\pmod4$, then
--
--   $$\nexists x,y\in\mathbb Z:\quad n=x^2+y^2\quad\text{and}\quad\gcd(x,y)=1.$$
--
--   The obstruction separates primitive representations from those obtained by scaling both coordinates.
-- source:
--   William Stein, Elementary Number Theory: Primes, Congruences, and Secrets, author-hosted 2017 PDF, Lemma 5.7.4 and Definition 5.7.3, printed pp. 118. https://wstein.org/ent/ent.pdf ; pinned author TeX commit c4984c7ddb22258674816f8c000b0d8eb485d694, body.tex lines 6927–6955: https://github.com/williamstein/ent/blob/c4984c7ddb22258674816f8c000b0d8eb485d694/body.tex

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace SteinENT
theorem no_primitive_representation (n p : ℕ) (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hmod : p % 4 = 3) :
    ¬ ∃ x y : ℤ, (n : ℤ) = x ^ 2 + y ^ 2 ∧ Int.gcd x y = 1 := by sorry
end SteinENT
