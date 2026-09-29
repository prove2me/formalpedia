-- Prove2me | Theorems.Thm_groupCohomology_infNatTrans_app_H2pi_carryFun_eq_card_nsmul
-- name    : groupCohomology.infNatTrans_app_H2pi_carryFun_eq_card_nsmul
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/63fdded1-2db2-590c-9eb8-498a9c91b43d
-- title:
--   Inflation multiplies a cyclic carry class by |N|
-- statement:
--   Let $G$ be a group and $s\in G$ an element of finite order such that every $g\in G$ lies in the subgroup of integer powers of $s$, so that $G$ is finite cyclic with generator $s$; let $N$ be a normal subgroup of $G$ and assume likewise that the image $\bar s$ of $s$ in $G/N$ has finite order and that every element of $G/N$ is an integer power of $\bar s$. For a $G$-representation $A$ over $\mathbb{Z}$, write $A^N$ for `A.quotientToInvariants N`, the module of $N$-invariants of $A$ viewed as a representation of $G/N$, and let $a\in A^N$, with underlying element $a.1\in A$. For a generator as above, the carry cochain `carryFun` attached to a coefficient $a$ is the function sending a pair $(g,h)$ to $a$ if $\mathrm{ord}(s)\le \ell(g)+\ell(h)$ and to $0$ otherwise, where $\ell(g)\in\{0,\dots,\mathrm{ord}(s)-1\}$ is the exponent with $s^{\ell(g)}=g$. Assume the carry cochain formed from $s$ and $a.1$ is a $2$-cocycle of $A$, and the carry cochain formed from $\bar s$ and $a$ is a $2$-cocycle of $A^N$. Then the degree-$2$ inflation map `(infNatTrans ℤ N 2).app A` sends the class in $H^2(G/N, A^N)$ of the latter cocycle to $\mathrm{card}(N)$ times the class in $H^2(G,A)$ of the former.
--
--   This is the cyclic-generator form of the rule $\mathrm{inf}\,u_{L/K} = [M:L]\,u_{M/K}$ for the canonical classes attached to cyclic extensions, expressed through explicit carry cocycles rather than through characters. It is used in the treatment of local fundamental classes and in the comparison of inflated classes with unit classes in the decomposition of places.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_infNatTrans_app_H2pi_carryFun_eq_card_nsmul.lean

import Mathlib
import Definitions.Def_GroupCohomology_CyclicCarry

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.infNatTrans_app_H2pi_carryFun_eq_card_nsmul
    {G : Type} [Group G] (s : G) (hs : ∀ g : G, g ∈ Subgroup.zpowers s) (hfin : IsOfFinOrder s)
    (N : Subgroup G) [N.Normal]
    (hsN : ∀ g : G ⧸ N, g ∈ Subgroup.zpowers (QuotientGroup.mk' N s)) (hsNfin : IsOfFinOrder (QuotientGroup.mk' N s))
    {A : Rep ℤ G} (a : A.quotientToInvariants N)
    (hc : carryFun (A := A) s hs hfin a.1 ∈ cocycles₂ A)
    (hcN : carryFun (QuotientGroup.mk' N s) hsN hsNfin a ∈ cocycles₂ (A.quotientToInvariants N)) :
    ((infNatTrans ℤ N 2).app A).hom
      ((H2π (A.quotientToInvariants N)).hom
        ⟨carryFun (QuotientGroup.mk' N s) hsN hsNfin a, hcN⟩) =
      Nat.card N • (H2π A).hom ⟨carryFun (A := A) s hs hfin a.1, hc⟩ := by sorry
