-- Prove2me | Theorems.Thm_diophantine_quintuple_acb_upper_bound
-- name    : diophantine_quintuple_acb_upper_bound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T06:42:59.245716+00:00
-- url     : https://prove2.me/theorems/e03ca55c-c9c4-4417-838e-502fe0e765c1
-- title:
--   Quintuple range upper bound (ac < 180.45 b^3)
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. Then $$20ac<3609b^3,\qquad\text{equivalently }ac<180.45b^3.$$ This is a uniform bound on the three smallest entries, with no degree hypothesis. Together with the non-Euler gap bound it gives the outer range for the five cases in Theorem 9. The source proves it by comparing $d>4abc$ with $d<721.8b^4$. Formalization note: $a=f_0$, $b=f_1$, and $c=f_2$, where `Quintuple f` and `Ordered f` express the ordered quintuple hypotheses.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 3, Lemma labelled lem:acb and its proof. The proof applies Lemma lem:cb to the irregular quadruple {a,b,d,e}, using b>3a from lem:b3a, and compares its bound d<721.8b^4 with d=d_+(a,b,c)>4abc from Fujita regularity and lem:d+ieq.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_acb_upper_bound (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) : f 0 * f 2 * 20 < 3609 * f 1 ^ 3 := by sorry
