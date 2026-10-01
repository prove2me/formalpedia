-- Prove2me | Theorems.Thm_burau_cf_std_add_divisor
-- name    : burau_cf_std_add_divisor
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:06:35.980978+00:00
-- url     : https://prove2.me/theorems/4e8fdd0c-8209-4397-a943-a4de67d4d471
-- title:
--   Shift lemma for the standard Euclidean continued fraction
-- statement:
--   **Shift lemma for the standard Euclidean continued fraction.** For $r\neq 0$,
--   $$ \mathtt{cfStd}(r,\ r+a) = \left(\frac{a}{r}+1\right) :: \mathtt{cfStd}\bigl(a\bmod r,\ r\bigr), $$
--   i.e. adding the divisor $r$ to the dividend increases the first quotient by one and leaves the remainder,
--   hence the whole tail, unchanged. This is exactly the step at which the two Euclidean descents appearing
--   in the continued-fraction analysis merge, and it is what makes the assembled two-branch formula for the
--   negative reciprocal of a rational a theorem rather than a numerical observation.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf

set_option autoImplicit false

theorem burau_cf_std_add_divisor (r a : ℤ) (hr : r ≠ 0) :
    cfStd r (r + a) = (a / r + 1) :: cfStd (a % r) r := by sorry
