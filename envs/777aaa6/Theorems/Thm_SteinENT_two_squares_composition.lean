-- Prove2me | Theorems.Thm_SteinENT_two_squares_composition
-- name    : SteinENT.two_squares_composition
-- status  : Proved
-- author  : @wamlart
-- created : 2026-09-06T01:23:41.614049+00:00
-- url     : https://prove2.me/theorems/666d5b65-ae21-4ad3-a1bd-0d96ddea9067
-- title:
--   Equation (5.7.1) — Composition of two-square representations
-- statement:
--   For any integers $x_1,y_1,x_2,y_2$,
--
--   $$(x_1^2+y_1^2)(x_2^2+y_2^2)=(x_1x_2-y_1y_2)^2+(x_1y_2+x_2y_1)^2.$$
--
--   The identity explicitly composes two representations and shows that represented integers are closed under multiplication.
-- source:
--   William Stein, Elementary Number Theory: Primes, Congruences, and Secrets, author-hosted 2017 PDF, Equation (5.7.1), printed pp. 119. https://wstein.org/ent/ent.pdf ; pinned author TeX commit c4984c7ddb22258674816f8c000b0d8eb485d694, body.tex lines 6978–6982: https://github.com/williamstein/ent/blob/c4984c7ddb22258674816f8c000b0d8eb485d694/body.tex

import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.NumberTheory.DiophantineApproximation.Basic
import Mathlib.Tactic

namespace SteinENT
theorem two_squares_composition (x₁ y₁ x₂ y₂ : ℤ) :
    (x₁ ^ 2 + y₁ ^ 2) * (x₂ ^ 2 + y₂ ^ 2) =
      (x₁ * x₂ - y₁ * y₂) ^ 2 + (x₁ * y₂ + x₂ * y₁) ^ 2 := by sorry
end SteinENT
