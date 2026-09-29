-- Prove2me | Theorems.Thm_groupCohomology_finite_groupCohomology_of_shortExact
-- name    : groupCohomology.finite_groupCohomology_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/1fcf5290-da3a-5b5e-946c-0f8a396cdd46
-- title:
--   Finiteness of Hⁿ(G,X₂) along a short exact sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, both in the same universe, and let $X$ be a short complex in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, that is, a pair of composable morphisms $X_1 \to X_2 \to X_3$ whose composite is zero. Assume $X$ is short exact, i.e. the first map is a monomorphism, the second an epimorphism, and the complex is exact in the middle. Let $n$ be a natural number, and assume that the group cohomology modules $H^n(G, X_1)$ and $H^n(G, X_3)$, formed by Mathlib's `groupCohomology` functor in degree $n$, are finite. The conclusion is that $H^n(G, X_2)$ is finite as well. No hypothesis is imposed on $G$ (no finiteness, no topology) or on $k$ beyond commutativity, and finiteness here is the bare `Finite` predicate on the underlying type, with no module- or group-structure refinement.
--
--   This is the standard two-out-of-three finiteness principle for group cohomology along a short exact sequence of coefficient modules, in a fixed degree. It is invoked in the present development through its degree-one and degree-two specialisations, [`groupCohomology.finite_H1_of_shortExact`](thm.html#groupCohomology.finite_H1_of_shortExact) and [`groupCohomology.finite_H2_of_shortExact`](thm.html#groupCohomology.finite_H2_of_shortExact).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_groupCohomology_of_shortExact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.finite_groupCohomology_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact) (n : ℕ)
    [Finite (groupCohomology X.X₁ n)] [Finite (groupCohomology X.X₃ n)] :
    Finite (groupCohomology X.X₂ n) := by sorry
