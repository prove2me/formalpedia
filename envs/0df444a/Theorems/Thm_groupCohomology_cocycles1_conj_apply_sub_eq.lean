-- Prove2me | Theorems.Thm_groupCohomology_cocycles1_conj_apply_sub_eq
-- name    : groupCohomology.cocycles1_conj_apply_sub_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/75045da8-81c1-5326-ab6d-0b24e8a49e44
-- title:
--   Conjugating a 1-cocycle changes it by a coboundary
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $A$ be a $k$-linear representation of $G$, i.e. an object of `Rep k G` with action maps $A.\rho$, and let $c$ be an element of `cocycles₁ A`, the $k$-submodule of functions $G \to A$ satisfying the inhomogeneous $1$-cocycle identity $c(gh) = A.\rho\,g\,(c(h)) + c(g)$ for all $g,h \in G$; $c$ is applied to group elements through this coercion to a function. Then for all $g, s \in G$,
--   $$A.\rho\,g\,\bigl(c(g^{-1} s g)\bigr) - c(s) \;=\; A.\rho\,s\,(c(g)) - c(g),$$
--   an identity in the underlying $k$-module of $A$. Thus the function $s \mapsto A.\rho\,g\,(c(g^{-1} s g))$, the $g$-conjugate of $c$, differs from $c$ by the principal $1$-coboundary attached to the element $c(g) \in A$.
--
--   This is the elementary half of the inflation–restriction statement at the term $H^1(S,A)^{G/S}$: for $S$ normal in $G$ the restriction to $S$ of a class in $H^1(G,A)$ is fixed by the conjugation action of $G/S$. It is used in the comparison of $H^1$ with its subgroup-invariant counterparts, via [`groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index`](thm.html#groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index) and [`groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq`](thm.html#groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_cocycles1_conj_apply_sub_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.cocycles1_conj_apply_sub_eq
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (c : cocycles₁ A) (g s : G) :
    A.ρ g (c (g⁻¹ * s * g)) - c s = A.ρ s (c g) - c g := by sorry
