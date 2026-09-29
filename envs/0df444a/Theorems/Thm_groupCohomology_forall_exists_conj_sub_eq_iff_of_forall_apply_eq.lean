-- Prove2me | Theorems.Thm_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq
-- name    : groupCohomology.forall_exists_conj_sub_eq_iff_of_forall_apply_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/7afdf5a7-c972-5f93-9536-2983b91b1015
-- title:
--   Conjugation invariance up to coboundaries under trivial S-action
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $A$ an object of `Rep k G` (a $k$-linear representation of $G$ with action map $A.\rho$), and $S \le G$ a subgroup. Assume that every element of $S$ acts trivially on $A$: for all $s \in S$ and all $v \in A$, $A.\rho\, s\, v = v$. Let $c$ be a $1$-cocycle of the restricted representation `Rep.res S.subtype A`, that is, of $A$ viewed as a representation of $S$ along the inclusion $S \hookrightarrow G$. The assertion is an equivalence of two conditions on $c$. The first: for every $g \in G$ there exists $a \in A$ such that for all $s, t \in S$ with $g^{-1} s g = t$ in $G$ one has $A.\rho\, g\, (c\,t) - c\,s = A.\rho\, s\, a - a$, i.e. the conjugation-translate of $c$ differs from $c$ by the coboundary attached to $a$. The second: for all $g \in G$ and all $s, t \in S$ with $g^{-1} s g = t$, one has $A.\rho\, g\, (c\,t) = c\,s$ exactly.
--
--   Since $S$ acts trivially on $A$, all $1$-coboundaries of $A|_S$ vanish, so invariance of a cocycle class under $G$-conjugation collapses to strict $G$-equivariance of $c \colon S \to A$ for the conjugation action on $S$. It is used in the computation of the rank of the module of continuous classes, [`groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq`](thm.html#groupCohomology.finrank_continuousClasses_eq_finrank_of_isUnit_index_of_forall_apply_eq).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_forall_exists_conj_sub_eq_iff_of_forall_apply_eq.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.forall_exists_conj_sub_eq_iff_of_forall_apply_eq
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G)
    (htriv : ∀ s ∈ S, ∀ v : A, A.ρ s v = v) (c : cocycles₁ (Rep.res S.subtype A)) :
    (∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
        A.ρ g (c t) - c s = A.ρ (s : G) a - a) ↔
      ∀ (g : G) (s t : S), (g⁻¹ * s * g : G) = t → A.ρ g (c t) = c s := by sorry
