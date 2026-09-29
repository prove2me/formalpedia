-- Prove2me | Theorems.Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_finite
-- name    : groupCohomology.natCard_H1_eq_natCard_H2_of_finite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/6fe9cbe4-1bf5-51d0-be70-74d678a5baaf
-- title:
--   Herbrand quotient one: #H¹ = #H² for finite cyclic G
-- statement:
--   Let $G$ be a group in the lowest universe which is finite and cyclic, and let $A$ be an object of `Rep ℤ G`, that is, a $\mathbb{Z}$-module carrying a $G$-action, whose underlying type is assumed finite. The conclusion is a threefold conjunction: the first cohomology group `H1 A` is finite, the second cohomology group `H2 A` is finite, and their cardinalities agree, $\operatorname{Nat.card}(H^1(G,A)) = \operatorname{Nat.card}(H^2(G,A))$, where `H1` and `H2` are Mathlib's group cohomology functors for the representation $A$ and `Nat.card` is the cardinality of a type (with the convention that it is $0$ for infinite types, here ruled out by the first two components). No hypothesis beyond finiteness of $G$, cyclicity of $G$ and finiteness of the underlying module of $A$ is imposed; in particular $A$ is not assumed to be a module over a coefficient ring other than $\mathbb{Z}$, and no nondegeneracy or torsion-freeness condition appears.
--
--   This is the statement that the Herbrand quotient $h(A) = \#H^2(G,A)/\#H^1(G,A)$ of a finite module over a finite cyclic group equals $1$ (Serre, Local Fields VIII §4). It is used in the project to compare cohomology cardinalities along short exact sequences, being cited by [`groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite`](thm.html#groupCohomology.natCard_H1_eq_natCard_H2_of_shortExact_of_subsingleton_of_finite).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_natCard_H1_eq_natCard_H2_of_finite.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory groupCohomology

theorem groupCohomology.natCard_H1_eq_natCard_H2_of_finite
    {G : Type} [Group G] [Finite G] [IsCyclic G] (A : Rep ℤ G) [Finite A] :
    Finite (H1 A) ∧ Finite (H2 A) ∧ Nat.card (H1 A) = Nat.card (H2 A) := by sorry
