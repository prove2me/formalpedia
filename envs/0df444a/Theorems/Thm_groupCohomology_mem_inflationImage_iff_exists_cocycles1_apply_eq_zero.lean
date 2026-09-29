-- Prove2me | Theorems.Thm_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
-- name    : groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/ac58d275-a06b-591b-995c-dbc88168e6cc
-- title:
--   Inflated classes are those with a cocycle vanishing on N
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, $M$ an object of `Rep k G`, that is a $k$-linear representation of $G$, and $N$ a normal subgroup of $G$; no triviality assumption is made on the action of $N$ on $M$. Let $x$ be an element of $H^1(G,M)$, in the form `H1 M`. The theorem asserts an equivalence. On one side, $x$ belongs to the $k$-submodule `inflationImage M N` of `H1 M`, defined as the range of the $k$-linear map underlying the inflation morphism $H^1(G/N, M^N) \to H^1(G,M)$, the latter being `groupCohomology.map` in degree $1$ applied to the quotient homomorphism $G \to G/N$ together with the morphism of representations obtained from the lift of $\rho$ to an action of $G/N$ on the $N$-invariants $M^N$. On the other side, there exists a $1$-cocycle $c$ of $G$ with values in $M$, an element of `cocycles₁ M`, whose cohomology class `H1π M c` is equal to $x$ and which satisfies $c(n) = 0$ for every $n \in N$.
--
--   This is the cocycle-level description of the image of inflation: a class comes from $H^1(G/N, M^N)$ exactly when it admits a representative cocycle vanishing identically on $N$, which is the usual consequence of the inflation–restriction exact sequence. It is used in the comparison of inflation images for different subgroups and in converting continuity and unramifiedness conditions on classes of a Galois group into membership in inflation images from finite levels, as in [`groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup`](thm.html#groupCohomology.exists_cocycles1_unramified_iff_mem_inflationImage_sup), [`groupCohomology.inflationImage_eq_inflationImage_of_forall_pow_mem`](thm.html#groupCohomology.inflationImage_eq_inflationImage_of_forall_pow_mem) and [`groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses`](thm.html#groupCohomology.invariants_add_dualTwist_le_finrank_continuousClasses).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_mem_inflationImage_iff_exists_cocycles1_apply_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_LocallyConstantClasses

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Module groupCohomology

universe u

theorem groupCohomology.mem_inflationImage_iff_exists_cocycles1_apply_eq_zero {k G : Type u} [CommRing k] [Group G] (M : Rep k G) (N : Subgroup G) [N.Normal] (x : H1 M) :
    x ∈ inflationImage M N ↔ ∃ c : cocycles₁ M, H1π M c = x ∧ ∀ n ∈ N, c n = 0 := by sorry
