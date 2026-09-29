-- Prove2me | Theorems.Thm_diophantine_quadruple_extension_criterion
-- name    : diophantine_quadruple_extension_criterion
-- status  : Open
-- author  : @xuanji
-- created : 2026-09-07T08:12:02.053769+00:00
-- url     : https://prove2.me/theorems/a907075f-8a50-4173-949f-618bfab43bf0
-- title:
--   Fujita-Miyazaki extension criterion (per-case thresholds)
-- statement:
--   Let $a<b<c<d$ be positive integers forming a Diophantine quadruple. Suppose one of the following conditions holds:
--
--   $$\begin{aligned}b<2a&\quad\text{and}\quad c\ge9.864b^4;\\2a\le b\le12a&\quad\text{and}\quad c\ge4.321b^4;\\b>12a&\quad\text{and}\quad c\ge721.8b^4.\end{aligned}$$
--
--   For natural-number square witnesses $r^2=ab+1$, $s^2=ac+1$, $t^2=bc+1$, the fourth entry is the regular extension: $$d=a+b+c+2abc+2rst.$$ Each threshold applies only in its stated ratio regime. The contrapositive bounds irregular quadruples and is used in the proof of the quintuple range bound. Formalization note: all six pairwise square conditions are explicit and the decimal thresholds are multiplied by 1000.
-- source:
--   Bo He, Alain Togbe, Volker Ziegler, arXiv:1610.04020v2, Lemma lem:cb (Theorem 1.5 of Y. Fujita and T. Miyazaki): let {a,b,c,d} be a Diophantine quadruple with a<b<c<d; if b<2a and c>=9.864b^4, or 2a<=b<=12a and c>=4.321b^4, or b>12a and c>=721.8b^4, then d = d_+. Used in Lemma lem:acb as `Hence, Lemma lem:cb provides d < 721.8b^4'. Source text: https://arxiv.org/abs/1610.04020v2.

import Definitions.Def_diophantine_descent
set_option autoImplicit false
open DiophantineDescent

theorem diophantine_quadruple_extension_criterion (a b c d : Nat)
    (ha : 0 < a) (hab : a < b) (hbc : b < c) (hcd : c < d)
    (hab2 : ∃ r : Nat, a * b + 1 = r ^ 2)
    (hac2 : ∃ s : Nat, a * c + 1 = s ^ 2)
    (hbc2 : ∃ t : Nat, b * c + 1 = t ^ 2)
    (had2 : ∃ u : Nat, a * d + 1 = u ^ 2)
    (hbd2 : ∃ v : Nat, b * d + 1 = v ^ 2)
    (hcd2 : ∃ w : Nat, c * d + 1 = w ^ 2)
    (r s t : Nat) (hr : a * b + 1 = r ^ 2)
    (hs : a * c + 1 = s ^ 2) (ht : b * c + 1 = t ^ 2)
    (hthresh : (b < 2 * a ∧ 9864 * b ^ 4 ≤ 1000 * c) ∨
      (2 * a ≤ b ∧ b ≤ 12 * a ∧ 4321 * b ^ 4 ≤ 1000 * c) ∨
      (12 * a < b ∧ 721800 * b ^ 4 ≤ 1000 * c)) :
    d = a + b + c + 2 * a * b * c + 2 * r * s * t := by sorry
