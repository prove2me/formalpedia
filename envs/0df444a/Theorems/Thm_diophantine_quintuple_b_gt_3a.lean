-- Prove2me | Theorems.Thm_diophantine_quintuple_b_gt_3a
-- name    : diophantine_quintuple_b_gt_3a
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T08:12:01.044666+00:00
-- url     : https://prove2.me/theorems/de8ab50a-278c-4212-acc6-508380edfd3c
-- title:
--   Quintuple gap b > 3a (Cipu-Filipin-Fujita)
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. Then $$b>3a.$$ This is the first assertion of the Cipu–Filipin–Fujita gap theorem. It excludes the smallest-ratio regime of the extension criterion and is a shared input to the quintuple range estimates. Formalization note: $a=f_0$ and $b=f_1$ for an ordered quintuple $f$.
-- source:
--   Bo He, Alain Togbe, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, Lemma lem:b3a, first assertion (Theorem 1.1 of M. Cipu, A. Filipin and Y. Fujita, Bounds for Diophantine quintuples II, Publ. Math. Debrecen 88 (2016), 59-78; see also Cipu-Fujita). Used in the proof of Lemma lem:acb as `From Lemma lem:b3a, we have b > 3a'. Source text: https://arxiv.org/abs/1610.04020v2.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_b_gt_3a (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) : 3 * f 0 < f 1 := by sorry
