-- Prove2me | Theorems.Thm_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index
-- name    : groupCohomology.mem_coboundaries1_of_restrict_of_isUnit_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/f8e3f4e2-672a-53ee-835f-bc4515e59d31
-- title:
--   Restriction to a finite-index subgroup is injective on H¹
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (in the same universe), let $A$ be a $k$-linear representation of $G$, i.e. an object of `Rep k G`, and let $S \le G$ be a subgroup of finite index whose index $[G:S]$, viewed in $k$ via the canonical map $\mathbb{N} \to k$, is a unit. Let $c$ be an element of `cocycles₁ A`, that is, a $1$-cocycle $c : G \to A$ for the $G$-action $\rho$ on $A$ (so $c(gg') = \rho(g)(c(g')) + c(g)$), regarded as a function by coercion. Assume that the restriction of $c$ to $S$ is a coboundary: there exists $a \in A$ with $c(s) = \rho(s)(a) - a$ for every $s \in S$. The conclusion is that $c$ itself is a coboundary on all of $G$: there exists $a \in A$ such that $c(g) = \rho(g)(a) - a$ for every $g \in G$. No normality assumption on $S$ is made, and the statement is at the level of cochains rather than cohomology classes.
--
--   This is the injectivity of the restriction map $H^1(G,A) \to H^1(S,A)$ when the index $[G:S]$ is invertible in the coefficient ring, stated on representatives. It is used to compare $H^1$ of a decomposition group with that of a subgroup in the local bridge lemmas [`NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge`](thm.html#NumberField.PlaceDecomp.exists_unit_inv_map_delta_res_eq_theta_localBridge) and its primary variant, and in [`groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index`](thm.html#groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_coboundaries1_of_restrict_of_isUnit_index.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.mem_coboundaries1_of_restrict_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G)
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (c : cocycles₁ A) (hc : ∃ a : A, ∀ s : S, c (s : G) = A.ρ (s : G) a - a) :
    ∃ a : A, ∀ g : G, c g = A.ρ g a - a := by sorry
