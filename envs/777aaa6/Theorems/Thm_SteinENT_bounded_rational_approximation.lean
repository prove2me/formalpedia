-- Prove2me | Theorems.Thm_SteinENT_bounded_rational_approximation
-- name    : SteinENT.bounded_rational_approximation
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:24:08.160454+00:00
-- url     : https://prove2.me/theorems/1872c98f-c9a0-440a-9c31-291b0f6c71d0
-- title:
--   Lemma 5.7.5 — Rational approximation with a bounded denominator
-- statement:
--   For a real number $x$ and a positive integer $n$, there is a reduced fraction $a/b$ with
--
--   $$0<b\le n,\qquad\left|x-\frac ab\right|\le\frac1{b(n+1)}.$$
--
--   The simultaneous denominator and error bounds provide the approximation input to the two-squares argument.
--
--   **Formalization Note** A rational number carries a reduced numerator and a positive denominator. Stein defines natural numbers as $\{1,2,3,\ldots\}$, so the Lean statement makes $n>0$ explicit.
-- source:
--   William Stein, Elementary Number Theory: Primes, Congruences, and Secrets, author-hosted 2017 PDF, Lemma 5.7.5, printed pp. 119. https://wstein.org/ent/ent.pdf ; pinned author TeX commit c4984c7ddb22258674816f8c000b0d8eb485d694, body.tex lines 6986–7011: https://github.com/williamstein/ent/blob/c4984c7ddb22258674816f8c000b0d8eb485d694/body.tex

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace SteinENT
theorem bounded_rational_approximation (x : ℝ) (n : ℕ) (hn : 0 < n) :
    ∃ q : ℚ, 0 < q.den ∧ q.den ≤ n ∧
      |x - q| ≤ 1 / ((q.den : ℝ) * (n + 1)) := by sorry
end SteinENT
