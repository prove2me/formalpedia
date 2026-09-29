-- Prove2me | Theorems.Thm_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso
-- name    : groupCohomology.isZero_H1_and_natCard_H2_and_span_map_of_iso
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/3a0848ba-33ba-5162-8b0e-62f8b203514f
-- title:
--   Class formation axioms transport along an isomorphism of G-modules
-- statement:
--   Let $G$ be a group, let $A$ and $B$ be $\mathbb{Z}$-linear representations of $G$ (objects of `Rep ℤ G`), let $e : A \cong B$ be an isomorphism in that category, and let $u$ be an element of $H^2(G, A)$, Mathlib's `groupCohomology A 2`. Assume three conditions for $A$: for every subgroup $S \le G$, the $\mathbb{Z}$-module $H^1(S, A)$ formed from the restricted representation `Rep.res S.subtype A` is a zero object; for every subgroup $S$ equipped with a `Fintype` structure, the cardinality of $H^2(S, A)$ equals the cardinality of $S$; and for every subgroup $S$, the $\mathbb{Z}$-span of the single element obtained by applying the restriction map `groupCohomology.map S.subtype (𝟙 _) 2` to $u$ is the whole of $H^2(S, A)$. The conclusion is the conjunction of the three corresponding assertions for $B$, with the distinguished class taken to be the image $e_*u$ of $u$ under `groupCohomology.map (MonoidHom.id G) e.hom 2`.
--
--   These are exactly the layer conditions occurring in the local and global class-formation statements of the project: vanishing of $H^1$, the order of $H^2$ over finite subgroups, and generation of $H^2(S,-)$ by the restriction of a fundamental class. The result lets those conditions be moved across an isomorphism of $G$-modules, and is used in the construction of fundamental classes for units of adic completions and in the extraction of local fundamental classes.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_isZero_H1_and_natCard_H2_and_span_map_of_iso.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.isZero_H1_and_natCard_H2_and_span_map_of_iso
    {G : Type} [Group G] (A B : Rep ℤ G) (e : A ≅ B) (u : groupCohomology A 2)
    (h1 : ∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype A) 1))
    (h2 : ∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype A) 2) = Fintype.card S)
    (h3 : ∀ S : Subgroup G,
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype A)) 2).hom u} = ⊤) :
    (∀ S : Subgroup G, CategoryTheory.Limits.IsZero (groupCohomology (Rep.res S.subtype B) 1)) ∧
    (∀ (S : Subgroup G) [Fintype S], Nat.card (groupCohomology (Rep.res S.subtype B) 2) = Fintype.card S) ∧
    (∀ S : Subgroup G,
      Submodule.span ℤ {(groupCohomology.map S.subtype (𝟙 (Rep.res S.subtype B)) 2).hom
        ((groupCohomology.map (MonoidHom.id G) e.hom 2).hom u)} = ⊤) := by sorry
