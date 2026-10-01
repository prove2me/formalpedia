-- Prove2me | Theorems.Thm_burau_cf_std_neg_of_dvd
-- name    : burau_cf_std_neg_of_dvd
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:19:58.645718+00:00
-- url     : https://prove2.me/theorems/c6eab1d8-16c3-485f-86fb-e64f83f4f12e
-- title:
--   Negation rule of continued fractions: the exact-division case
-- statement:
--   **Negation of a continued fraction, exact-division case.** If $b\mid a$ then the continued
--   fraction of $-a/b$ is the single negative quotient
--   $$ \mathtt{cfStd}(b,\,-a) = \left[-\frac{a}{b}\right], $$
--   so the transformation $x\mapsto -x$ is trivial on rationals with terminating expansion. It is the base
--   case of the negation rule, the companion of the negative-reciprocal rule, and together they describe how
--   the descent of the pair $(b,-a)$ — the pair produced by right multiplication by the standard generator
--   $S$ of $\mathrm{SL}(2,\mathbb Z)$ — relates to that of $(a,b)$.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf

set_option autoImplicit false

theorem burau_cf_std_neg_of_dvd (a b : ℤ) (ha : 0 < a) (hb : 0 < b) (hdvd : b ∣ a) :
    cfStd b (-a) = [-(a / b)] := by sorry
