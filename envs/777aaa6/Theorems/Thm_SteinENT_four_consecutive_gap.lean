-- Prove2me | Theorems.Thm_SteinENT_four_consecutive_gap
-- name    : SteinENT.four_consecutive_gap
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:24:34.996869+00:00
-- url     : https://prove2.me/theorems/0e55107d-231b-42de-8553-7b05ba14cfb7
-- title:
--   Exercise 5.11 — Every four consecutive integers contain a two-square gap
-- statement:
--   For every integer $n$, at least one member of the block $n,n+1,n+2,n+3$ is not a sum of two integer squares:
--
--   $$\exists k\in\{0,1,2,3\}\quad\nexists x,y\in\mathbb Z:\ n+k=x^2+y^2.$$
--
--   This gives a uniform bound on the length of consecutive runs of represented integers.
-- source:
--   William Stein, Elementary Number Theory: Primes, Congruences, and Secrets, author-hosted 2017 PDF, Exercise 5.11, printed pp. 122. https://wstein.org/ent/ent.pdf ; pinned author TeX commit c4984c7ddb22258674816f8c000b0d8eb485d694, body.tex lines 7183–7184: https://github.com/williamstein/ent/blob/c4984c7ddb22258674816f8c000b0d8eb485d694/body.tex

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace SteinENT
theorem four_consecutive_gap (n : ℤ) :
    ∃ k : ℤ, 0 ≤ k ∧ k < 4 ∧ ¬ ∃ x y : ℤ, n + k = x ^ 2 + y ^ 2 := by sorry
end SteinENT
