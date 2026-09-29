-- Prove2me | Theorems.Thm_groupCohomology_map_coindFunctor_map_comp_coindIso_hom
-- name    : groupCohomology.map_coindFunctor_map_comp_coindIso_hom
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/a9892044-5d58-5e1f-a055-f28d8fd95c1b
-- title:
--   Naturality of Shapiro's isomorphism in the coefficients
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $S \le G$ be a subgroup, let $A$ and $B$ be $k$-linear representations of $S$, i.e. objects of `Rep k S`, let $\varphi : A \to B$ be a morphism of such representations, and let $n$ be a natural number. The coinduction functor `Rep.coindFunctor k S.subtype` along the inclusion `S.subtype : S →* G` carries $\varphi$ to a morphism $\operatorname{coind}_S^G A \to \operatorname{coind}_S^G B$ of representations of $G$, and `groupCohomology.map` applied to the identity homomorphism of $G$ and to this morphism gives the induced map $H^n(G, \operatorname{coind}_S^G A) \to H^n(G, \operatorname{coind}_S^G B)$; likewise `groupCohomology.map` applied to the identity homomorphism of $S$ and to $\varphi$ gives $H^n(S,A) \to H^n(S,B)$. Writing `groupCohomology.coindIso A n` for Shapiro's isomorphism $H^n(G, \operatorname{coind}_S^G A) \cong H^n(S,A)$, the assertion is the commutativity of the square: the induced map on $H^n(G,-)$ followed by the forward direction of Shapiro's isomorphism for $B$ equals the forward direction of Shapiro's isomorphism for $A$ followed by the induced map on $H^n(S,-)$.
--
--   This is the naturality of Shapiro's (Eckmann–Shapiro) isomorphism with respect to change of coefficient representation, in each cohomological degree. It is used in the construction relating corestriction, restriction and norm maps, where the semilocal description of cohomology must be transported along maps of coefficient modules.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_map_coindFunctor_map_comp_coindIso_hom.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.map_coindFunctor_map_comp_coindIso_hom
    {k G : Type u} [CommRing k] [Group G] {S : Subgroup G} {A B : Rep k S} (φ : A ⟶ B) (n : ℕ) :
    groupCohomology.map (MonoidHom.id G) ((Rep.coindFunctor k S.subtype).map φ) n ≫
        (groupCohomology.coindIso B n).hom =
      (groupCohomology.coindIso A n).hom ≫ groupCohomology.map (MonoidHom.id S) φ n := by sorry
