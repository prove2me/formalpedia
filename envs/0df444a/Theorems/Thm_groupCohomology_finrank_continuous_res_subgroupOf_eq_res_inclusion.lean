-- Prove2me | Theorems.Thm_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion
-- name    : groupCohomology.finrank_continuous_res_subgroupOf_eq_res_inclusion
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/37e183d4-1671-5729-85e3-2df357acd679
-- title:
--   Invariants and continuous H¹, H² under reindexing S'≤ S
-- statement:
--   Let $k$ be a field and $G$ a group (in the same universe), let $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ be a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, let $S' \le S$ be subgroups of $G$ with $hle \colon S' \le S$, and let $N$ be a $k$-linear representation of $S$. The subgroup $S'$ may be presented either as the subgroup `S'.subgroupOf S` of $S$, restricting $N$ along its inclusion `(S'.subgroupOf S).subtype` and taking the level map $r$ composed with `S.subtype` and then with that inclusion, or directly as $S'$, restricting $N$ along `Subgroup.inclusion hle` and taking the level map $r$ composed with `S'.subtype`. The theorem asserts three equalities of $k$-dimensions between the two presentations: for the submodules of invariants of the two restricted representations; for the submodules `continuousH1` of $H^1$, each defined as the image under the projection $H1\pi$ of the submodule `levelCocycles₁` of $1$-cocycles attached to the respective level map; and for the types `continuousH2`, each defined as the quotient of `levelCocycles₂` by the submodule of `levelCoboundaries₂` lying inside it for the respective level map.
--
--   This is a bookkeeping compatibility statement: passing from a subgroup of a subgroup to a subgroup of the ambient group changes neither the invariants nor the continuous $H^1$ and $H^2$ dimensions. It is used in [`groupCohomology.euler_poincare_identity_of_hypotheses`](thm.html#groupCohomology.euler_poincare_identity_of_hypotheses), where the induction proving the local Euler–Poincaré identity replaces the ambient group by an open subgroup, while the Shapiro-type inputs are formulated for subgroups of the ambient group.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_finrank_continuous_res_subgroupOf_eq_res_inclusion.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map
import Definitions.Def_GroupCohomology_ContinuousH1

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.finrank_continuous_res_subgroupOf_eq_res_inclusion {k G : Type u} [Field k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S' S : Subgroup G) (hle : S' ≤ S) (N : Rep.{u} k S) :
    Module.finrank k (Rep.res (S'.subgroupOf S).subtype N).ρ.invariants
        = Module.finrank k (Rep.res (Subgroup.inclusion hle) N).ρ.invariants ∧
    Module.finrank k (groupCohomology.continuousH1 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH1 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) ∧
    Module.finrank k (groupCohomology.continuousH2 ((r.comp S.subtype).comp (S'.subgroupOf S).subtype)
          (Rep.res (S'.subgroupOf S).subtype N))
        = Module.finrank k (groupCohomology.continuousH2 (r.comp S'.subtype) (Rep.res (Subgroup.inclusion hle) N)) := by sorry
