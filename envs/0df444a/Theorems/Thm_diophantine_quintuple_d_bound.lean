-- Prove2me | Theorems.Thm_diophantine_quintuple_d_bound
-- name    : diophantine_quintuple_d_bound
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:47:19.60995+00:00
-- url     : https://prove2.me/theorems/35ed081f-d2bf-49c2-beb6-edca21bef124
-- title:
--   Diophantine quintuple: $d<1.83\cdot10^{52}$
-- statement:
--   Let $\{a,b,c,d,e\}$ be a Diophantine quintuple listed in increasing order, so that $a<b<c<d<e$ are positive integers and $xy+1$ is a perfect square for every two distinct members $x,y$. Then the fourth element satisfies
--
--   $$d < 1.83\cdot 10^{52}.$$
--
--   This is the second of the two numerical bounds established in Proposition 5 of He–Togbé–Ziegler. It bounds the size of the quintuple itself and is what reduces the problem to a finite search, whereas the companion bound $ac<6.77\cdot10^{25}$ controls the initial triple. The two are proved by different estimates and are used at different points, so they are stated separately.
--
--   Here the indices are those of the labelling $f:\mathrm{Fin}\,5	o\mathbb N$, so $d=f(3)$.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 7, Proposition 5. That proposition asserts the two bounds $ac<6.77\cdot10^{25}$ and $d<1.83\cdot10^{52}$ jointly; this lemma isolates one of them.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_d_bound (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) :
    f 3 < 18300000000000000000000000000000000000000000000000000 := by sorry
