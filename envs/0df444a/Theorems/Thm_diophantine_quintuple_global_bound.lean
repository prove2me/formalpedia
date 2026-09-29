-- Prove2me | Theorems.Thm_diophantine_quintuple_global_bound
-- name    : diophantine_quintuple_global_bound
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T02:46:45.039772+00:00
-- url     : https://prove2.me/theorems/06b8fe7b-5969-4b51-bc5c-515a705c27ad
-- title:
--   Global bounds for a quintuple (Proposition 5)
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. Then $$ac<6.77\cdot 10^{{25}}\quad\text{and}\quad d<1.83\cdot 10^{{52}}.$$ This is the numerical part of Proposition 5 (Section 7), proved via linear forms in logarithms (Theorems 5–6). It is the shared global estimate used by the proofs of Theorems 8 and 9 to cap the subsequent finite searches; the companion Pell-exponent bound is stated separately.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 7, Proposition 5 (bounds $ac<6.77\cdot 10^{25}$, $d<1.83\cdot 10^{52}$).

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_global_bound (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) :
    f 0 * f 2 < 67700000000000000000000000 ∧ f 3 < 18300000000000000000000000000000000000000000000000000 := by sorry
