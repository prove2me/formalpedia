-- Prove2me | Theorems.Thm_groupCohomology_finrank_inflationImage_le_finrank_invariants
-- name    : groupCohomology.finrank_inflationImage_le_finrank_invariants
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/ee79adb7-9929-5c4d-b965-4bb87cca9475
-- title:
--   Inflation image in H¹ bounded by invariants, cyclic quotient
-- statement:
--   Let $k$ be a field and $G$ a group (in the same universe), let $M$ be a $k$-linear representation of $G$ whose underlying $k$-module is finite-dimensional, and let $N$ be a normal subgroup of $G$ of finite index. Suppose there is an element $\varphi \in G$ whose class in $G/N$ generates $G/N$, in the sense that every $x \in G/N$ lies in the subgroup of integer powers of $\varphi \bmod N$. Then the $k$-dimension of [`groupCohomology.inflationImage M N`](def/GroupCohomology_LocallyConstantClasses.html#L21) is at most the $k$-dimension of the space $M^G$ of invariants of the representation $\rho$ of $M$. Here `inflationImage M N` is the submodule of $H^1(G, M)$ given by the range of the underlying $k$-linear map of the inflation morphism, namely the degree-one functoriality map `groupCohomology.map` attached to the projection $G \to G/N$ together with the map of representations lifting the inclusion of the $N$-invariants $M^N$, regarded as a representation of $G/N$, into $M$; thus the assertion is $\dim_k \operatorname{im}\bigl(H^1(G/N, M^N) \to H^1(G, M)\bigr) \le \dim_k M^G$. No finiteness is assumed of $G$ itself.
--
--   This is the bound of the image of inflation in $H^1$ by the dimension of the $H^0$-part, for a finite cyclic quotient $G/N$ of an otherwise arbitrary group $G$ — typically $G$ a local absolute Galois group and $N$ the kernel of a finite cyclic character of it. It feeds the count of unramified continuous classes used in the deformation-theoretic dimension estimates, being cited by [`ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth`](thm.html#ExtCitation.finrank_unramifiedContinuousClasses_eq_finrank_invariants_of_cyclic_of_depth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_inflationImage_le_finrank_invariants.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.finrank_inflationImage_le_finrank_invariants
    {k G : Type u} [Field k] [Group G] (M : Rep k G) [FiniteDimensional k M]
    (N : Subgroup G) [N.Normal] [N.FiniteIndex]
    {φ : G} (hφ : ∀ x : G ⧸ N, x ∈ Subgroup.zpowers (QuotientGroup.mk φ : G ⧸ N)) :
    Module.finrank k (groupCohomology.inflationImage M N) ≤ Module.finrank k M.ρ.invariants := by sorry
