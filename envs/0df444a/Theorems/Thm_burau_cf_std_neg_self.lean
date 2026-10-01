-- Prove2me | Theorems.Thm_burau_cf_std_neg_self
-- name    : burau_cf_std_neg_self
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T22:16:59.861272+00:00
-- url     : https://prove2.me/theorems/53b65bb1-a6c3-41c0-bfc2-07d86ab6130f
-- title:
--   Negative reciprocal of one: base case of the continued-fraction rule
-- statement:
--   **Base case of the negative-reciprocal rule of continued fractions.** For $a\neq 0$,
--   $$ \mathtt{cfStd}(a,\ -a) = [-1], $$
--   the continued fraction of $-1/1=-1$. This is the base case of the inductive analysis of the
--   transformation $x\mapsto-1/x$: with the shift lemma and the two explicit branches for $b/a=1$ and
--   $b/a\ge 2$ it anchors the computation of the quotient list of $-1/x$ from that of $x$, which is the
--   continued-fraction input of the three-strand Burau faithfulness reduction.
-- source:
--   Euclidean continued fractions; cf. A. Ya. Khinchin, *Continued Fractions* (1964), Ch. II.

import Definitions.Def_burau_std_cf

set_option autoImplicit false

theorem burau_cf_std_neg_self (a : ℤ) (ha : a ≠ 0) :
    cfStd a (-a) = [-1] := by sorry
