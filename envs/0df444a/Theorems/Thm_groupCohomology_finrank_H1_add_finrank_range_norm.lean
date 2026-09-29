-- Prove2me | Theorems.Thm_groupCohomology_finrank_H1_add_finrank_range_norm
-- name    : groupCohomology.finrank_H1_add_finrank_range_norm
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/ca92563f-38ff-55cd-8553-1c3bd6bb738e
-- title:
--   Dimension formula for H¹ of a finite cyclic group
-- statement:
--   Let $k$ be a field, $G$ a group, and $A$ a representation of $G$ over $k$, i.e. an object of `Rep k G`, with $G$ finite and $A$ finite-dimensional as a $k$-vector space. Suppose there is an element $g \in G$ such that every element of $G$ lies in `Subgroup.zpowers g`, the subgroup of integer powers of $g$; that is, $G$ is cyclic with generator $g$. Then the $k$-dimensions of three spaces are related by
--   $$\dim_k H^1(G,A) + \dim_k \operatorname{im}(N) = \dim_k A^G,$$
--   where $H^1(G,A)$ is `groupCohomology.H1 A` with its $k$-module structure, $N =$ `A.ρ.norm` is the $k$-linear endomorphism $\sum_{x \in G} \rho(x)$ of $A$, $\operatorname{im}(N)$ is its range as a $k$-submodule, and $A^G$ is the submodule `A.ρ.invariants` of vectors fixed by every $\rho(x)$. All three dimensions are taken in the sense of `Module.finrank`. In particular the formula gives $\dim_k H^1(G,A) \le \dim_k A^G$, with equality exactly when the norm endomorphism vanishes.
--
--   This is the standard dimension count for the cohomology of a finite cyclic group in degree $1$, obtained from the identification of cocycles with the kernel of the norm via evaluation at the generator together with rank–nullity. It serves as the finite-level input for bounding $H^1$ of a group with cyclic quotient and for the count of unramified classes at a place away from the residue characteristic, and is cited by [`groupCohomology.finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient`](thm.html#groupCohomology.finrank_H1_le_finrank_invariants_add_finrank_ker_of_cyclic_quotient) and [`groupCohomology.finrank_inflationImage_le_finrank_invariants`](thm.html#groupCohomology.finrank_inflationImage_le_finrank_invariants).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_H1_add_finrank_range_norm.lean

import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.Data.ZMod.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory Module

theorem groupCohomology.finrank_H1_add_finrank_range_norm
    {k G : Type u} [Field k] [Group G] (A : Rep k G) [Fintype G] [FiniteDimensional k A]
    {g : G} (hg : ∀ x, x ∈ Subgroup.zpowers g) :
    finrank k (groupCohomology.H1 A) + finrank k (LinearMap.range A.ρ.norm)
      = finrank k A.ρ.invariants := by sorry
