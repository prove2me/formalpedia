-- Prove2me | Theorems.Thm_groupCohomology_subsingleton_H2_of_isUnit_card
-- name    : groupCohomology.subsingleton_H2_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/96f98213-72b1-577f-b211-295d9bb9b8c8
-- title:
--   Vanishing of H² when |G| is invertible
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$ be an object of `Rep k G`, that is a $k$-linear representation of $G$ on a $k$-module with action $A.\rho$. Assume `hG`: the image of the cardinality $\#G$ under the canonical ring map $\mathbb{N} \to k$ is a unit of $k$. The conclusion is that `groupCohomology.H2 A` is a subsingleton: any two elements of the second group cohomology of $G$ with coefficients in $A$, formed in Mathlib as the quotient of the module of inhomogeneous $2$-cocycles `groupCohomology.cocycles₂ A` by the submodule of $2$-coboundaries `groupCohomology.coboundaries₂ A`, are equal. Since $H^2(G,A)$ carries a module structure, this is the assertion that it vanishes. Note that finiteness of $G$ enters only through the `Fintype` structure used to form $\#G$ and the averaging sums, and no hypothesis is imposed on $k$ beyond commutativity.
--
--   This is the degree-$2$ instance of the classical averaging (or transfer) argument showing that the cohomology of a finite group vanishes in positive degrees once the group order is invertible in the coefficient ring. It is used in the level-arithmetic part of the development, in [`NumberField.LevelArith.exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep`](thm.html#NumberField.LevelArith.exists_level_coboundary_of_isPGroup_of_map_diag_H2pi_eq_zero_sUnitsMaxRep), where an obstruction class in $H^2$ is killed because the relevant group has order coprime to the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_subsingleton_H2_of_isUnit_card.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open CategoryTheory in

theorem groupCohomology.subsingleton_H2_of_isUnit_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H2 A) := by sorry
