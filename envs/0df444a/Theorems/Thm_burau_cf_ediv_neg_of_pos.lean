-- Prove2me | Theorems.Thm_burau_cf_ediv_neg_of_pos
-- name    : burau_cf_ediv_neg_of_pos
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:28:39.680293+00:00
-- url     : https://prove2.me/theorems/956478ad-6396-4013-a729-b956422bf4f8
-- title:
--   Euclidean division of a negated dividend (ceiling form)
-- statement:
--   **Euclidean division of a negated dividend.** For positive integers $a,b$, the Euclidean
--   quotient of $-a$ by $b$ is minus the ceiling of $a/b$:
--   $$ \frac{-a}{b} = -\left\lceil \frac{a}{b}\right\rceil = -\frac{a+b-1}{b}, $$
--   where the last quotient is the integer division. This uniform formula (no case distinction on the size
--   of $a$ and $b$) is the arithmetic input that makes the continued-fraction rule $x\mapsto -1/x$ a single
--   recursion instead of a case analysis; it is used in the Euclidean-descent analysis of
--   $\mathrm{SL}(2,\mathbb Z)$ behind the three-strand Burau faithfulness statement.
-- source:
--   Euclidean algorithm on Z; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Mathlib

set_option autoImplicit false

theorem burau_cf_ediv_neg_of_pos (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    (-a) / b = -((a + b - 1) / b) := by sorry
