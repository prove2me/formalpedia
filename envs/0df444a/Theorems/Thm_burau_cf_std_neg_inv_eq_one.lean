-- Prove2me | Theorems.Thm_burau_cf_std_neg_inv_eq_one
-- name    : burau_cf_std_neg_inv_eq_one
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T21:58:54.831985+00:00
-- url     : https://prove2.me/theorems/49a03e48-3f73-4081-aa46-9e657b94fa7f
-- title:
--   Negative reciprocal: the branch b/a = 1
-- statement:
--   **First branch of the negative-reciprocal rule of continued fractions.** If $a>0$ and the
--   continued fraction of $b/a$ begins with $1$ (i.e. $b/a=1$ in integer division) then
--   $$ \mathtt{cfStd}(b,\,-a) = [-1] \mathbin{+\!+} \bigl((y+1) :: \mathrm{tail}\,y\bigr),\qquad
--   y = \mathtt{cfStd}(b-a,\ a), $$
--   i.e. the expansion of $-1/x$ is obtained from that of $1/(x-1)$ by lowering the first quotient by one and
--   prefixing $-1$. Numerically this is the branch that matched in all 54 tested cases; here it is a theorem.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf

set_option autoImplicit false

theorem burau_cf_std_neg_inv_eq_one (a b : ℤ) (ha : 0 < a) (h : b / a = 1) :
    cfStd b (-a) = [-1] ++ (match cfStd (b - a) a with
                            | [] => []
                            | y :: ys => (y + 1) :: ys) := by sorry
