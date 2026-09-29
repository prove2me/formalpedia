-- Prove2me | Theorems.Thm_groupCohomology_finite_H1_of_shortExact
-- name    : groupCohomology.finite_H1_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/007de1d3-d2eb-5cfe-b633-80bf82700da1
-- title:
--   Finiteness of H¹ in the middle of a short exact sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, both in the same universe, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed to be short exact, that is, the first map is a monomorphism, the second is an epimorphism, and the complex is exact at the middle term. Assume that the first cohomology groups $H^1(G, X_1)$ and $H^1(G, X_3)$ of the outer terms are finite (finiteness being asserted of the underlying types of `H1 X.X₁` and `H1 X.X₃`). The conclusion is that $H^1(G, X_2)$ is finite as well. No hypothesis is placed on $G$ (it need not be finite or profinite) or on $k$ beyond commutativity, and no finiteness of the underlying modules is assumed.
--
--   This is the degree-one instance of the standard two-out-of-three finiteness statement for the long exact sequence of group cohomology attached to a short exact sequence of representations. It is used in the comparison of the orders of $H^1$ and $H^2$ for finite cyclic groups, via [`groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_H1_of_shortExact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.finite_H1_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H1 X.X₁)] [Finite (H1 X.X₃)] :
    Finite (H1 X.X₂) := by sorry
