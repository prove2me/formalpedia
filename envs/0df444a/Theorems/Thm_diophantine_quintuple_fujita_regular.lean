-- Prove2me | Theorems.Thm_diophantine_quintuple_fujita_regular
-- name    : diophantine_quintuple_fujita_regular
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T08:12:01.367564+00:00
-- url     : https://prove2.me/theorems/9268817c-4e0a-4da3-b4a4-3811702b8e72
-- title:
--   Fujita regularity of {a,b,c,d} (explicit d_+ equation)
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple. There exist nonnegative integers $r,s,t$ such that $$r^2=ab+1,\quad s^2=ac+1,\quad t^2=bc+1,$$ and $$d=a+b+c+2abc+2rst.$$ Thus the first four entries form a regular Diophantine quadruple. This is the Fujita regularity theorem used throughout the source paper; combined with elementary square-product estimates it supplies the lower bound $d>4abc$. Formalization note: the regular-extension formula uses explicit natural-number square witnesses.
-- source:
--   Bo He, Alain Togbe, Volker Ziegler, arXiv:1610.04020v2, Theorem thm:fujita (Y. Fujita, Any Diophantine quintuple contains a regular Diophantine quadruple, J. Number Theory 129 (2009), 1678–1697): if {a,b,c,d,e} is a quintuple with a<b<c<d<e then the quadruple {a,b,c,d} is regular. Used in Lemma lem:acb as `By Fujita's result, the quadruple {a,b,c,d} is regular' and `we have d = d_+ > 4abc'. Source text: https://arxiv.org/abs/1610.04020v2.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_fujita_regular (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) :
    ∃ r s t : Nat, f 0 * f 1 + 1 = r ^ 2 ∧ f 0 * f 2 + 1 = s ^ 2 ∧
      f 1 * f 2 + 1 = t ^ 2 ∧
      f 3 = f 0 + f 1 + f 2 + 2 * f 0 * f 1 * f 2 + 2 * r * s * t := by sorry
