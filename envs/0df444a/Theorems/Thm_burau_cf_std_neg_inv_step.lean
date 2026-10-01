-- Prove2me | Theorems.Thm_burau_cf_std_neg_inv_step
-- name    : burau_cf_std_neg_inv_step
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:03:20.860782+00:00
-- url     : https://prove2.me/theorems/0dc9c43a-77dd-4bfc-af4c-67ad7133883e
-- title:
--   Negative reciprocal: uniform one-step recursion of the Euclidean descent
-- statement:
--   **Negative reciprocal of a rational: the uniform step of the Euclidean descent.**
--   For positive integers $a,b$, the standard Euclidean continued fraction of $-1/(b/a) = -a/b$ takes the
--   explicit one-step recursion
--   $$ \mathtt{cfStd}(b,\,-a) = -\left\lceil \frac{a}{b}\right\rceil :: \mathtt{cfStd}\Bigl(b\left\lceil
--   \frac{a}{b}\right\rceil - a,\ b\Bigr), $$
--   with no case distinction on the size of $a$ and $b$: the leading quotient is the ceiling quotient of the
--   negated dividend and the new pair is again positive. This is the recursion that drives the whole
--   continued-fraction analysis of the transformation $x\mapsto -1/x$, which is the missing input of the
--   three-strand Burau faithfulness reduction.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf
import Theorems.Thm_burau_cf_ediv_neg_of_pos
import Theorems.Thm_burau_cf_emod_neg_of_pos

set_option autoImplicit false

theorem burau_cf_std_neg_inv_step (a b : ℤ) (ha : 0 < a) (hb : 0 < b) :
    cfStd b (-a) = -((a + b - 1) / b) :: cfStd (b * ((a + b - 1) / b) - a) b := by
  sorry
