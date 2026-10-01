-- Prove2me | Theorems.Thm_burau_cf_ediv_neg_ge_one
-- name    : burau_cf_ediv_neg_ge_one
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:48:07.360586+00:00
-- url     : https://prove2.me/theorems/b7b2287d-0fd5-4829-8489-dc509a824579
-- title:
--   Negative reciprocal: first step of the Euclidean descent (quotient)
-- statement:
--   **First step of the negative-reciprocal rule of continued fractions (quotient form).**
--   If $a>0$ and the leading quotient of the continued fraction of $b/a$ is at least $1$ — equivalently
--   $b\ge a$ — then the Euclidean quotient of $-a$ by $b$ is $-1$:
--   $$ \frac{-a}{b} = -1 . $$
--   Combined with the companion remainder identity $(-a)\bmod b=b-a$ this says that the descent of the pair
--   $(b,-a)$ starts with the quotient $-1$ and continues from the pair $(b-a,b)$, which is the mechanism by
--   which the two Euclidean descents used in the $\mathrm{SL}(2,\mathbb Z)$ continued-fraction section merge.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_ediv_neg_ge_one (a b : ℤ) (ha : 0 < a) (h : 1 ≤ b / a) :
    (-a) / b = -1 := by sorry
