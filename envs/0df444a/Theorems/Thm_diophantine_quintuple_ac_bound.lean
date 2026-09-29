-- Prove2me | Theorems.Thm_diophantine_quintuple_ac_bound
-- name    : diophantine_quintuple_ac_bound
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:47:16.64662+00:00
-- url     : https://prove2.me/theorems/b6890c8c-210f-4fd7-a378-8f6d4edf20cb
-- title:
--   Diophantine quintuple: $ac<6.77\cdot10^{25}$
-- statement:
--   Let $\{a,b,c,d,e\}$ be a Diophantine quintuple listed in increasing order, so that $a<b<c<d<e$ are positive integers and $xy+1$ is a perfect square for every two distinct members $x,y$. Then the product of the smallest and the third smallest element is bounded by
--
--   $$ac < 6.77\cdot 10^{25}.$$
--
--   This is the first of the two numerical bounds established in Proposition 5 of He–Togbé–Ziegler. It is the bound consumed by the later case analysis: each of the degree-$\ge 2$ case lemmas of this mission takes $ac<6.77\cdot10^{25}$ as a hypothesis, so isolating it makes it directly reusable rather than reachable only through the combined statement.
--
--   Here the indices are those of the labelling $f:\mathrm{Fin}\,5	o\mathbb N$, so $a=f(0)$ and $c=f(2)$.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; Section 7, Proposition 5. That proposition asserts the two bounds $ac<6.77\cdot10^{25}$ and $d<1.83\cdot10^{52}$ jointly; this lemma isolates one of them.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_ac_bound (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) :
    f 0 * f 2 < 67700000000000000000000000 := by sorry
