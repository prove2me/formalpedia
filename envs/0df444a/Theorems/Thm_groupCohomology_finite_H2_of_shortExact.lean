-- Prove2me | Theorems.Thm_groupCohomology_finite_H2_of_shortExact
-- name    : groupCohomology.finite_H2_of_shortExact
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/6a298878-d2be-5562-9279-e4678c4aa5e3
-- title:
--   Finiteness of H² in the middle of a short exact sequence
-- statement:
--   Let $k$ be a commutative ring and $G$ a group, and let $X$ be a short complex $X_1 \to X_2 \to X_3$ in the category $\mathrm{Rep}\,k\,G$ of $k$-linear representations of $G$, assumed short exact in the sense of `ShortComplex.ShortExact`, that is, the first map is a monomorphism, the second an epimorphism, and the complex is exact at the middle term. Assume that the second group cohomology $H^2(G, X_1)$ of the sub-object and the second group cohomology $H^2(G, X_3)$ of the quotient are both finite types. The conclusion is that $H^2(G, X_2)$ is a finite type as well. Here $H^2$ is Mathlib's `H2` for a representation, the degree-$2$ group cohomology of $G$ with coefficients in the given representation. No hypotheses are imposed on $G$ (no finiteness, no topology) or on $k$ beyond commutativity.
--
--   This is the degree-$2$ instance of the standard two-out-of-three finiteness statement along the long exact cohomology sequence attached to a short exact sequence of coefficient modules. It is used in the computations of orders of cohomology groups for representations of finite cyclic groups, in particular by the comparisons [`groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite) and [`groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial`](thm.html#groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finite_H2_of_shortExact.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.finite_H2_of_shortExact
    {k G : Type u} [CommRing k] [Group G] {X : ShortComplex (Rep k G)} (hX : X.ShortExact)
    [Finite (H2 X.X₁)] [Finite (H2 X.X₃)] :
    Finite (H2 X.X₂) := by sorry
