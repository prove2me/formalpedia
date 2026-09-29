-- Prove2me | Theorems.Thm_groupCohomology_exists_map_eq_of_directed_of_injective
-- name    : groupCohomology.exists_map_eq_of_directed_of_injective
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/531b26e1-9260-5650-8e2b-a9b76212dd56
-- title:
--   Classes in Hⁿ(G,B) come from a member of a directed family
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $I$ be a preorder that is directed with respect to $\le$. Let $B$ be a $k$-linear representation of $G$, let $A : I \to \mathrm{Rep}\,k\,G$ be a family of representations, and let $\iota_i : A_i \to B$ be morphisms of representations such that: each underlying $k$-linear map $(\iota_i)_{\mathrm{hom}}$ is injective; the ranges increase, i.e. $\mathrm{range}\,(\iota_i)_{\mathrm{hom}} \subseteq \mathrm{range}\,(\iota_j)_{\mathrm{hom}}$ whenever $i \le j$; and the ranges cover $B$, i.e. every element $b$ of the underlying module of $B$ lies in $\mathrm{range}\,(\iota_i)_{\mathrm{hom}}$ for some $i$. Then for every natural number $n$, every class $x \in H^n(G, B)$ and every index $i_0$, there exist $i \ge i_0$ and a class $y \in H^n(G, A_i)$ whose image under the map on group cohomology induced by the identity of $G$ and $\iota_i$, namely `groupCohomology.map (MonoidHom.id G) (ι i) n`, equals $x$. Only this surjectivity statement is asserted; nothing is claimed about kernels, and no general compatibility of cohomology with filtered colimits is claimed.
--
--   This is the surjectivity half of the standard fact that the cohomology of a finite group commutes with directed unions of coefficient modules: every class with coefficients in $B$ already comes from a sufficiently large member of the directed family, and one may moreover demand the index to dominate any prescribed $i_0$. It is used for idèle-type coefficient modules, which are directed unions of their $S$-level submodules, in [`M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles`](thm.html#M4aHerbrand.injective_and_finite_and_surjective_localCoordinates_groupCohomology_ideles).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_map_eq_of_directed_of_injective.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open CategoryTheory

theorem groupCohomology.exists_map_eq_of_directed_of_injective
    {k G : Type u} [CommRing k] [Group G] [Finite G]
    {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    {B : Rep k G} (A : I → Rep k G) (ι : ∀ i, A i ⟶ B) (hι : ∀ i, Function.Injective (ι i).hom)
    (hmono : ∀ i j, i ≤ j → Set.range (ι i).hom ⊆ Set.range (ι j).hom)
    (hcov : ∀ b : B, ∃ i, b ∈ Set.range (ι i).hom)
    (n : ℕ) (x : groupCohomology B n) (i₀ : I) :
    ∃ i, i₀ ≤ i ∧ ∃ y : groupCohomology (A i) n, (groupCohomology.map (MonoidHom.id G) (ι i) n).hom y = x := by sorry
