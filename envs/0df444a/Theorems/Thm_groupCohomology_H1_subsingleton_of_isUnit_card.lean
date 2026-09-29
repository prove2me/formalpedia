-- Prove2me | Theorems.Thm_groupCohomology_H1_subsingleton_of_isUnit_card
-- name    : groupCohomology.H1.subsingleton_of_isUnit_card
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/3cd10113-f968-5bf4-a5d2-e12741e46fd3
-- title:
--   Vanishing of H¹ when |G| is invertible
-- statement:
--   Let $k$ be a commutative ring and $G$ a finite group, and let $A$ be an object of `Rep k G`, that is, a $k$-linear representation of $G$ with structure map $\rho$. Assume that the image of the cardinality of $G$ under the canonical map $\mathbb{N} \to k$ is a unit in $k$. The conclusion is that the first group cohomology `groupCohomology.H1 A` is a subsingleton: any two of its elements are equal. Since $H^1(G,A)$ carries a $k$-module structure, this is exactly the assertion $H^1(G,A) = 0$; here $H^1$ is Mathlib's first cohomology of the representation $A$, computed as the quotient of the module of inhomogeneous $1$-cocycles `groupCohomology.cocycles₁ A`, the functions $f : G \to A$ satisfying $f(gh) = \rho(g)(f(h)) + f(g)$, by the submodule of $1$-coboundaries `groupCohomology.coboundaries₁ A`, the functions of the form $g \mapsto \rho(g)(a) - a$ for some $a \in A$.
--
--   This is the standard vanishing of first cohomology of a finite group whose order is invertible in the coefficient ring, the Maschke-type argument in degree one. It is used in the project by [`groupCohomology.injective_H1_restriction_of_isUnit_index`](thm.html#groupCohomology.injective_H1_restriction_of_isUnit_index), and thereby in the local analysis of Galois cohomology at primes where the relevant inertia quotients have order prime to the residue characteristic.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_H1_subsingleton_of_isUnit_card.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u
open CategoryTheory in

theorem groupCohomology.H1.subsingleton_of_isUnit_card
    {k G : Type u} [CommRing k] [Group G] [Fintype G] (A : Rep k G)
    (hG : IsUnit ((Fintype.card G : k))) :
    Subsingleton (groupCohomology.H1 A) := by sorry
