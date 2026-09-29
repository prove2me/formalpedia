-- Prove2me | Theorems.Thm_diophantine_quintuple_abde_irregular
-- name    : diophantine_quintuple_abde_irregular
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T08:12:04.250002+00:00
-- url     : https://prove2.me/theorems/b85ec2c0-178d-46ac-84da-b95acc773dab
-- title:
--   Irregularity of {a,b,d,e} in a quintuple
-- statement:
--   Let $a<b<c<d<e$ be a Diophantine quintuple, and choose natural-number witnesses $$r^2=ab+1,\qquad s^2=ad+1,\qquad t^2=bd+1.$$ Then $$e
--   e a+b+d+2abd+2rst.$$ In other words, the quadruple formed by the first, second, fourth, and fifth entries is irregular. This is the explicit irregularity assertion used in the source's proof of the quintuple range bound to apply the extension criterion contrapositively. It is stated as a separate obligation because that proof asserts irregularity without a derivation at that point.
-- source:
--   Bo He, Alain Togbe, Volker Ziegler, arXiv:1610.04020v2, proof of Lemma lem:acb: `By Fujita's result (Theorem thm:fujita), the Diophantine quadruple {a,b,c,d} is regular. Consider the irregular Diophantine quadruple {a,b,d,e}.' No lemma number or justification is given for the irregularity; it is isolated here as an explicit child rather than silently assumed. Source text: https://arxiv.org/abs/1610.04020v2.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_abde_irregular (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f) (r s t : Nat)
    (hr : f 0 * f 1 + 1 = r ^ 2) (hs : f 0 * f 3 + 1 = s ^ 2)
    (ht : f 1 * f 3 + 1 = t ^ 2) :
    f 4 ≠ f 0 + f 1 + f 3 + 2 * f 0 * f 1 * f 3 + 2 * r * s * t := by sorry
