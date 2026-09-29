-- Prove2me | Theorems.Thm_diophantine_quadruple_extension_small_ratio
-- name    : diophantine_quadruple_extension_small_ratio
-- status  : Open
-- author  : @cm_beta
-- created : 2026-09-20T19:57:19.278664+00:00
-- url     : https://prove2.me/theorems/dab98a31-9579-432e-82dd-ba6b89618624
-- title:
--   Quadruple extension, regime $b<2a$
-- statement:
--   Let $a<b<c<d$ be positive integers forming a Diophantine quadruple, so that the product of any two of them increased by one is a perfect square, and let $r,s,t$ be square roots with $ab+1=r^{2}$, $ac+1=s^{2}$ and $bc+1=t^{2}$. Under the regime hypothesis below, the quadruple is regular:
--
--   $$d = a+b+c+2abc+2rst.$$
--
--   This is the small-ratio regime: $b<2a$, with the threshold $9.864\,b^{4}\le c$.
--
--   The extension criterion of He–Togbé–Ziegler is stated with a hypothesis that is a disjunction of three regimes, distinguished by the size of $b$ relative to $a$, each carrying its own explicit lower bound on $c$. The three regimes are handled by different estimates in the source, so each is stated here as a lemma in its own right; together they recover the original criterion by case analysis on the disjunction.
-- source:
--   Bo He, Alain Togbé, Volker Ziegler, There is no Diophantine quintuple, arXiv:1610.04020v2, https://arxiv.org/abs/1610.04020v2; the quadruple extension criterion, whose hypothesis is a three-way case distinction on the ratio $b/a$ with a different explicit threshold on $c$ in each regime. This lemma is one of those three regimes.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quadruple_extension_small_ratio (a b c d : Nat)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hab2 : ∃ r : Nat, a * b + 1 = r ^ 2)
    (hac2 : ∃ s : Nat, a * c + 1 = s ^ 2)
    (hbc2 : ∃ t : Nat, b * c + 1 = t ^ 2)
    (had2 : ∃ u : Nat, a * d + 1 = u ^ 2)
    (hbd2 : ∃ v : Nat, b * d + 1 = v ^ 2)
    (hcd2 : ∃ w : Nat, c * d + 1 = w ^ 2)
    (r s t : Nat) (hr : a * b + 1 = r ^ 2)
    (hs : a * c + 1 = s ^ 2) (ht : b * c + 1 = t ^ 2)
    (hlt : b < 2 * a) (hthr : 9864 * b ^ 4 ≤ 1000 * c) :
    d = a + b + c + 2 * a * b * c + 2 * r * s * t := by sorry
