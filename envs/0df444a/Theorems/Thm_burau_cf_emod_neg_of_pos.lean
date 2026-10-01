-- Prove2me | Theorems.Thm_burau_cf_emod_neg_of_pos
-- name    : burau_cf_emod_neg_of_pos
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:35:46.217621+00:00
-- url     : https://prove2.me/theorems/2598c453-d644-4554-a2cd-221276e220ca
-- title:
--   Euclidean remainder of a negated dividend
-- statement:
--   **Euclidean remainder of a negated dividend.** For positive integers $a,b$,
--   $$ (-a)\bmod b = b\left\lceil \frac{a}{b}\right\rceil - a = b\cdot\frac{a+b-1}{b} - a, $$
--   the companion of the quotient formula $-a/b=-\lceil a/b\rceil$. Together they give the one-step recursion
--   of the standard Euclidean continued fraction of $-\frac1x$ in terms of that of $x$, i.e. the negative
--   reciprocal transformation of continued fractions.
-- source:
--   Euclidean algorithm on Z; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_emod_neg_of_pos (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (-a) % b = b * ((a + b - 1) / b) - a := by sorry
