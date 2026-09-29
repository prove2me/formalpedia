-- Prove2me | Theorems.Thm_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient
-- name    : groupCohomology.Kummer.natCard_H1_eq_natCard_quotient
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f83ae7d6-cf51-5ebc-bcb3-f05f81c9b01c
-- title:
--   Kummer isomorphism as a cardinality identity
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra that is finite-dimensional over $K$ and Galois over $K$, and let $p$ be a natural number. Write $G = L \simeq_{\mathrm{alg}[K]} L$ for the group of $K$-algebra automorphisms of $L$, and let `kummerRep K L p` be the $\mathbb{Z}$-representation of $G$ obtained from the multiplicative-distributive action of $G$ on the group $\mu_p(L)$ of $p$-th roots of unity in $L$. Let `powerSubgroup K L p` be the subgroup of $K^\times$ consisting of those units $a$ for which the image of $a$ under the structure map $K \to L$ equals $\alpha^p$ for some $\alpha \in L^\times$. The assertion is an equality of natural-number cardinalities: the cardinality of the first group cohomology $H^1$ of `kummerRep K L p` equals the cardinality of the quotient of `powerSubgroup K L p` by the subgroup induced on it by the range of the $p$-th power endomorphism of $K^\times$, i.e. by $(K^\times)^p$ viewed inside `powerSubgroup K L p`. Both sides are `Nat.card`, so the statement is about the sizes of the two groups rather than about an isomorphism.
--
--   This is the counting form of the Kummer isomorphism $\bigl(K^\times \cap (L^\times)^p\bigr)/(K^\times)^p \cong H^1(\mathrm{Gal}(L/K), \mu_p(L))$ for a finite Galois extension. It is used to compute the order of the automorphism group in [`KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient`](thm.html#KummerTheory.natCard_algEquiv_eq_natCard_powerSubgroup_quotient).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_natCard_H1_eq_natCard_quotient.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.natCard_H1_eq_natCard_quotient
    {K L : Type} [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L] (p : ℕ) :
    Nat.card (H1 (kummerRep K L p))
      = Nat.card (powerSubgroup K L p ⧸
          ((powMonoidHom p : Kˣ →* Kˣ).range).subgroupOf (powerSubgroup K L p)) := by sorry
