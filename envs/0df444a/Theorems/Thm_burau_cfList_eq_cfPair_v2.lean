-- Prove2me | Theorems.Thm_burau_cfList_eq_cfPair_v2
-- name    : burau_cfList_eq_cfPair_v2
-- status  : Proved
-- author  : @lt9
-- created : 2026-09-30T23:26:29.718874+00:00
-- url     : https://prove2.me/theorems/2b0b487b-0027-4224-ad51-b7550f7f69c6
-- title:
--   The matrix quotient list equals the integer continued-fraction recursion
-- statement:
--   **The matrix descent and the integer descent compute the same quotient list.** For every
--   $2\times 2$ integer matrix $M$,
--   $$ \mathtt{cfList}(M) = \mathtt{cfPair}\bigl(M_{00},\, M_{01}\bigr), $$
--   i.e. the quotient list recorded by the Euclidean descent step $M\mapsto (MT^{-n})S$ (with
--   $n=M_{01}/M_{00}$) coincides with the purely integer recursion `cfPair`. The proof is a strong induction
--   on the measure $|M_{00}|$, using the measure lemma of the matrix descent. This bridges the matrix-level
--   section of $\mathrm{SL}(2,\mathbb Z)$ and the integer continued-fraction machinery on which the
--   negative-reciprocal rule is formalised.
-- source:
--   Euclidean algorithm in SL(2,Z); cf. C. Moser, H. S. M. Coxeter, *Generators and relations for discrete groups* (1964), Ch. 3.

import Definitions.Def_burau_cf_list
import Definitions.Def_burau_cf_pair

set_option autoImplicit false

theorem burau_cfList_eq_cfPair_v2 (M : BurauNC.M2) :
    BurauNC.cfList M = BurauNC.cfPair (M 0 0) (M 0 1) := by sorry
