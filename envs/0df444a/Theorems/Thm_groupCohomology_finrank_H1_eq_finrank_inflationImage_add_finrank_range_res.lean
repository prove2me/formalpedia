-- Prove2me | Theorems.Thm_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res
-- name    : groupCohomology.finrank_H1_eq_finrank_inflationImage_add_finrank_range_res
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/22c84d8f-0676-5dce-9e4a-f294e288b32d
-- title:
--   Rank decomposition of H¹ along inflation–restriction
-- statement:
--   Let $k$ be a field and $G$ a group (both in the same universe), let $A$ be a $k$-linear representation of $G$, and let $S$ be a normal subgroup of $G$; assume the first group cohomology $H^1(G,A)$ is finite-dimensional over $k$. Then $$\dim_k H^1(G,A) \;=\; \dim_k\bigl(\mathrm{inflationImage}\,A\,S\bigr) \;+\; \dim_k\bigl(\operatorname{im} g\bigr),$$ where the first summand is the image of the inflation map, namely the range of the $k$-linear map underlying `inflation A S`, the degree-$1$ cohomology map induced by the quotient homomorphism $G \to G/S$ together with the equivariant map from the $S$-invariants $A^S$ (as a $G/S$-representation) to $A$, so that `inflation A S` goes $H^1(G/S, A^S) \to H^1(G,A)$; and the second summand is the range of the $k$-linear map underlying the second map $g$ of Mathlib's inflation–restriction short complex `H1InfRes A S`, i.e. the image of the restriction $H^1(G,A) \to H^1(S,A)$. Thus the dimension of $H^1(G,A)$ is the dimension of the inflation image plus the dimension of the image of restriction to $S$.
--
--   This is the rank form of the inflation–restriction exact sequence in degree one: the classes inflated from $G/S$ (the "unramified" part in the Galois setting, where $S$ is the image of inertia) account for exactly the kernel of restriction, so the two summands measure the unramified and the ramified contributions. It is used in the dévissage bounding $\dim_k H^1$ of a tame local Galois group, in particular by [`groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth`](thm.html#groupCohomology.finrank_invariants_add_finrank_ker_le_finrank_H1_of_depth).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_H1_eq_finrank_inflationImage_add_finrank_range_res.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.finrank_H1_eq_finrank_inflationImage_add_finrank_range_res {k G : Type u} [Field k] [Group G] (A : Rep k G) (S : Subgroup G) [S.Normal]
    [FiniteDimensional k (H1 A)] :
    finrank k (H1 A) = finrank k (inflationImage A S) +
      finrank k (LinearMap.range (ModuleCat.Hom.hom (H1InfRes A S).g)) := by sorry
