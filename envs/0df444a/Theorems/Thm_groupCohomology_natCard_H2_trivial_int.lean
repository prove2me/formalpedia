-- Prove2me | Theorems.Thm_groupCohomology_natCard_H2_trivial_int
-- name    : groupCohomology.natCard_H2_trivial_int
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6b825344-63a4-552e-a3bd-3ce9b0437eb3
-- title:
--   #H²(G,ℤ) = #G for finite cyclic G
-- statement:
--   Let $G$ be a group in the lowest universe, assumed finite and cyclic. Form the trivial representation `Rep.trivial ℤ G ℤ`, that is, the $\mathbb{Z}$-module $\mathbb{Z}$ with $G$ acting by the identity, viewed as an object of the category of $\mathbb{Z}$-linear representations of $G$. The assertion is an equality of natural numbers: the cardinality of the underlying type of the second group cohomology $H^2(\mathrm{Rep.trivial}\ \mathbb{Z}\ G\ \mathbb{Z})$, measured by `Nat.card`, equals the cardinality `Nat.card G` of $G$. Since `Nat.card` returns $0$ for infinite types, the statement includes the information that $H^2(G,\mathbb{Z})$ is finite of order exactly $\#G$, the finiteness of $G$ guaranteeing that the right-hand side is positive.
--
--   This is the classical computation $H^2(G,\mathbb{Z}) \cong \widehat{H}^0(G,\mathbb{Z}) = \mathbb{Z}/\#G\,\mathbb{Z}$ for a finite cyclic group acting trivially, one of the two inputs (alongside the vanishing of $H^1(G,\mathbb{Z})$) to the Herbrand-quotient bookkeeping for cyclic groups. It is used by [`groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial`](thm.html#groupCohomology.natCard_H2_eq_natCard_of_shortExact_of_iso_trivial), where the order of $H^2$ of a representation is compared with $\#G$ through a short exact sequence whose outer terms are trivial.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H2_trivial_int.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H2_trivial_int
    {G : Type} [Group G] [Finite G] [IsCyclic G] :
    Nat.card (H2 (Rep.trivial ℤ G ℤ)) = Nat.card G := by sorry
