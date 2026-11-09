-- Prove2me | Theorems.Thm_CouretOaiBridge01_NORM02_prime_center_label_unique
-- name    : CouretOaiBridge01.NORM02.prime_center_label_unique
-- status  : Proved
-- author  : @alexcour
-- created : 2026-11-08T21:00:38.382047+00:00
-- url     : https://prove2.me/theorems/69adf14a-5c06-40ed-8b97-b887326c8c2c
-- title:
--   A small-index center has a unique large-prime label
-- statement:
--   Let P,p,q,m,n be natural numbers. Suppose p,q are prime, P<p and P<q, 0<m<P, 0<n<P, and pm=qn. Then $$p=q.$$ Both index positivity hypotheses and both strict upper bounds are explicit.
-- source:
--   Alexandre Couret, https://github.com/alexcour/couret-finite-verifications/blob/9c1b4e471ddf8ead0392fcc412f5dd8f8f910eb5/research/lean/CouretOaiBridge01/NORM02_FiniteArithmetic.lean#L51-L84, lines 51–84; source file SHA-256 8a9082ec16916ce79648638644c086bc87becdd9603b3fe3314147ab2c5feab3; theorem CouretOaiBridge01.NORM02.prime_center_label_unique

import Mathlib
import Mathlib

/-!
# NORM-02 — finite arithmetic certification layer

This file formalizes elementary, reusable sublemmas of NORM-01:
* exact coverage of the middle tent window by fixed anchor indices;
* primality and coprimality of those anchor indices;
* unique prime label for small-index centers;
* finite bad-square counting budget;
* the rational constant 3/50 in the mass lower bound.

Not formalized here: the 2026 Matomäki–Radziwill–Shao–Tao–Teräväinen
short-interval theorem, the asymptotic exceptional-set estimate, the full
squarefree sieve or the normalized Möbius correlation asymptotics.

RESEARCH ONLY. No sorry, no axioms added, no RH claim, no novelty claim.
-/

namespace CouretOaiBridge01
namespace NORM02

theorem prime_center_label_unique
    (P p q m n : ℕ)
    (hp : Nat.Prime p) (hq : Nat.Prime q)
    (hpP : P < p) (hqP : P < q)
    (hm : 0 < m) (hn : 0 < n)
    (hmP : m < P) (hnP : n < P)
    (heq : p * m = q * n) :
    p = q := by sorry






end NORM02
end CouretOaiBridge01
