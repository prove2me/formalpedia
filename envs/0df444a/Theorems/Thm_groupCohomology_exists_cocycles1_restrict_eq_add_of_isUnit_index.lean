-- Prove2me | Theorems.Thm_groupCohomology_exists_cocycles1_restrict_eq_add_of_isUnit_index
-- name    : groupCohomology.exists_cocycles1_restrict_eq_add_of_isUnit_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/a07eaf6a-575d-5a5b-a85c-ab74399b5f18
-- title:
--   Restriction in degree one is surjective at invertible index
-- statement:
--   Let $k$ be a commutative ring, $G$ a group and $A$ a $k$-linear representation of $G$; let $S$ be a normal subgroup of $G$ of finite index, and suppose the image of $[G:S]$ in $k$ is a unit. Let $c$ be a $1$-cocycle of the restricted representation $A|_S$, i.e. an element of `cocycles₁ (Rep.res S.subtype A)`, so $c : S \to A$ satisfies $c(st) = \rho(s)c(t) + c(s)$ for $s,t \in S$. Assume that the class of $c$ is invariant under conjugation by $G$ at cocycle level: for every $g \in G$ there is $a \in A$ such that for all $s,t \in S$ with $g^{-1}sg = t$ one has $\rho(g)c(t) - c(s) = \rho(s)a - a$. Then there exist a $1$-cocycle $c'$ of $G$ with values in $A$ (an element of `cocycles₁ A`) and an element $a \in A$ such that $c'(s) = c(s) + (\rho(s)a - a)$ for every $s \in S$; that is, $c$ agrees up to the coboundary of $a$ with the restriction of $c'$ to $S$.
--
--   This is the surjectivity half of inflation–restriction in degree one when the index is invertible: the restriction map $H^1(G,A) \to H^1(S,A)^{G/S}$ hits every $G/S$-invariant class, stated at the level of cocycles rather than cohomology classes. It feeds the construction of the isomorphism [`groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index`](thm.html#groupCohomology.exists_linearEquiv_H1_of_forall_iff_of_isUnit_index) between $H^1$ of $G$ and the invariants in $H^1$ of $S$.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_cocycles1_restrict_eq_add_of_isUnit_index.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.exists_cocycles1_restrict_eq_add_of_isUnit_index
    {k G : Type u} [CommRing k] [Group G] (A : Rep.{u} k G) (S : Subgroup G) [S.Normal]
    [S.FiniteIndex] (hindex : IsUnit ((S.index : k)))
    (c : cocycles₁ (Rep.res S.subtype A))
    (hc : ∀ g : G, ∃ a : A, ∀ s t : S, (g⁻¹ * s * g : G) = t →
      A.ρ g (c t) - c s = A.ρ (s : G) a - a) :
    ∃ (c' : cocycles₁ A) (a : A), ∀ s : S, c' (s : G) = c s + (A.ρ (s : G) a - a) := by sorry
