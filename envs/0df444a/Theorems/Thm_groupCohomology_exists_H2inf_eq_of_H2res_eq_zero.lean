-- Prove2me | Theorems.Thm_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero
-- name    : groupCohomology.exists_H2inf_eq_of_H2res_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/52137eaf-74aa-5700-a859-0ddd1685d494
-- title:
--   Inflation surjects onto the kernel of restriction on H²
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a $k$-linear representation of $G$, and let $S$ be a normal subgroup of $G$. Assume that $H^1$ of the restriction of $A$ to $S$ (the representation `Rep.res S.subtype A`) is a subsingleton, i.e. that $H^1(S,A)=0$. Let $x$ be a class in $H^2(G,A)$ whose image under the restriction map in degree $2$ — the map `groupCohomology.map` associated with the inclusion $S \hookrightarrow G$ and the identity morphism of the restricted representation, so $H^2(G,A) \to H^2(S,A)$ — vanishes. Then there exists a class $y$ in $H^2(G/S, A^S)$, the cohomology of the $G/S$-representation `A.quotientToInvariants S` on the $S$-invariants of $A$, whose image under the inflation map in degree $2$ — the map `groupCohomology.map` associated with the projection $G \to G/S$ together with the canonical morphism of $G$-representations $A^S \to A$ — equals $x$. Thus inflation surjects onto the kernel of restriction in degree $2$.
--
--   This is the exactness at $H^2(G,A)$ of the inflation–restriction sequence $H^2(G/S,A^S) \to H^2(G,A) \to H^2(S,A)$ under the hypothesis $H^1(S,A)=0$, the case $q=2$ of the classical inflation–restriction exact sequence. It is used in the bound [`groupCohomology.finite_H2_and_natCard_H2_le`](thm.html#groupCohomology.finite_H2_and_natCard_H2_le) on the size of second cohomology groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_H2inf_eq_of_H2res_eq_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology Rep

theorem groupCohomology.exists_H2inf_eq_of_H2res_eq_zero
    {k G : Type u} [CommRing k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [Subsingleton (H1 (Rep.res S.subtype A))] (x : H2 A)
    (hx : (groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom x = 0) :
    ∃ y : H2 (A.quotientToInvariants S),
      (groupCohomology.map (A := A.quotientToInvariants S) (B := A)
        (QuotientGroup.mk' S) (Rep.ofHom (A.ρ.quotientToInvariants_lift S)) 2).hom y = x := by sorry
