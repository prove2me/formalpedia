-- Prove2me | Theorems.Thm_diophantine_quintuple_fujita_d_formula
-- name    : diophantine_quintuple_fujita_d_formula
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:54:43.296576+00:00
-- url     : https://prove2.me/theorems/96c08fe4-5104-4d7e-a0c9-115e0061fb85
-- title:
--   Regularity formula: $d=a+b+c+2abc+2rst$
-- statement:
--   Let $\{a,b,c,d,e\}$ be a Diophantine quintuple listed in increasing order, with $a=f(0)$, $b=f(1)$, $c=f(2)$ and $d=f(3)$. Suppose $r,s,t$ are non-negative integers with
--
--   $$ab+1=r^{2},\qquad ac+1=s^{2},\qquad bc+1=t^{2}.$$
--
--   Then the fourth element is given by the regularity formula
--
--   $$d = a+b+c+2abc+2rst.$$
--
--   In other words, the quadruple $\{a,b,c,d\}$ is regular: $d$ is the larger of the two values that extend the triple $\{a,b,c\}$, and it is determined by $a,b,c$ together with the chosen square roots. This is Fujita's regularity statement as used by He–Togbé–Ziegler.
--
--   The lemma is stated with $r,s,t$ universally quantified rather than existentially bound. That is deliberate: the existence of such $r,s,t$ is immediate from the definition of a Diophantine quintuple, so the mathematical content lies entirely in the formula for $d$. Quantifying them universally lets the formula be applied to any admissible choice of square roots at the point of use, instead of forcing a caller to accept opaque witnesses.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; the regularity of the quadruple $\{a,b,c,d\}$, following Fujita. This lemma states the formula for $d$ in terms of given square roots $r,s,t$, which is the mathematical content of the existential form of the statement.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quintuple_fujita_d_formula (f : Fin 5 → Nat)
    (hq : Quintuple f) (ho : Ordered f)
    (r s t : Nat) (hr : f 0 * f 1 + 1 = r ^ 2) (hs : f 0 * f 2 + 1 = s ^ 2)
    (ht : f 1 * f 2 + 1 = t ^ 2) :
    f 3 = f 0 + f 1 + f 2 + 2 * f 0 * f 1 * f 2 + 2 * r * s * t := by sorry
