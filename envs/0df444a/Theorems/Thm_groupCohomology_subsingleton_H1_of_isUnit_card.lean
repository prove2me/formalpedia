-- Prove2me | Theorems.Thm_groupCohomology_subsingleton_H1_of_isUnit_card
-- name    : groupCohomology.subsingleton_H1_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/516608ff-2c5e-5414-b04d-15c7fe417950
-- title:
--   Vanishing of H¹ when |G| is invertible
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$ be an object of `Rep k G`, that is, a $k$-module equipped with a $k$-linear action $\rho$ of $G$. Assume that the image of the cardinality of $G$ under the canonical map $\mathbb{N} \to k$ is a unit of $k$. The conclusion is that the first group cohomology `groupCohomology.H1 A`, the cohomology of $A$ in degree one in the sense of Mathlib's inhomogeneous cochain complex, is a subsingleton: any two of its elements are equal, so the group $H^1(G,A)$ is trivial. Note that the hypothesis is invertibility in $k$ of the order of $G$ as a scalar, no assumption being made on $A$ beyond its being a $k$-linear representation.
--
--   This is the classical averaging argument showing that the cohomology of a finite group vanishes in positive degrees once the group order is invertible in the coefficient ring, here in degree one. It is used in the project as the source of injectivity in inflation–restriction arguments, for instance in comparing $H^1$ of a group with $H^1$ of a subgroup of invertible index, and feeds into the Greenberg–Wiles style computations of Selmer groups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_subsingleton_H1_of_isUnit_card.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory
open CategoryTheory in

theorem groupCohomology.subsingleton_H1_of_isUnit_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) := by sorry
