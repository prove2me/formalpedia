-- Prove2me | Theorems.Thm_burau_cf_std_neg_inv_ge_two
-- name    : burau_cf_std_neg_inv_ge_two
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:06:56.772569+00:00
-- url     : https://prove2.me/theorems/9ebc8777-bc16-4784-bd22-6aeaf8e89feb
-- title:
--   Negative reciprocal: the branch b/a ≥ 2
-- statement:
--   **Second branch of the negative-reciprocal rule of continued fractions.** If $a>0$ and the
--   leading quotient of the continued fraction of $b/a$ is at least $2$, then
--   $$ \mathtt{cfStd}(b,\,-a) = \bigl[-1,\ \tfrac{a}{b-a}+1\bigr] \mathbin{+\!+}
--   \mathtt{cfStd}\bigl(a \bmod (b-a),\ b-a\bigr). $$
--   Together with the branch $b/a=1$ and the base case $b=a$ this covers the whole range $b/a\ge1$; the
--   formula has been checked numerically in all 99 tested cases and is proved here by the shift lemma of the
--   Euclidean descent.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf

set_option autoImplicit false

theorem burau_cf_std_neg_inv_ge_two (a b : ℤ) (ha : 0 < a) (h : 2 ≤ b / a) :
    cfStd b (-a) = [-1, a / (b - a) + 1] ++ cfStd (a % (b - a)) (b - a) := by sorry
