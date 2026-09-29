-- Prove2me | Theorems.Thm_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq
-- name    : groupCohomology.exists_coind_cocycles1_isLevelConstant1_eval_one_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/99ca3e82-c9c6-5732-8f47-c7035a0102ff
-- title:
--   Degree-one Shapiro lifting of level-constant cocycles
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $r \colon G \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$, and let $S$ be a subgroup of $G$ which is assumed open for the level topology in the following sense: there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that the $r$-preimage of the fixing subgroup of $F_0$ is contained in $S$. Let $N$ be a $k$-linear representation of $S$ and let $b$ be a $1$-cocycle of $S$ with values in $N$, assumed to satisfy the predicate [`groupCohomology.IsLevelConstant₁`](def/GroupCohomology_ContinuousH2.html#L14) for the composite of the inclusion $S \hookrightarrow G$ with $r$. The conclusion asserts the existence of a $1$-cocycle $c$ of $G$ with values in the coinduced representation `Rep.coind S.subtype N` which satisfies [`groupCohomology.IsLevelConstant₁`](def/GroupCohomology_ContinuousH2.html#L14) for $r$ itself and whose values restrict back to $b$ in the sense that, for every $s \in S$, the function $G \to N$ underlying $c(s)$ takes the value $b(s)$ at $1 \in G$. No normality, finite-index or continuity hypothesis on $S$ beyond the stated openness condition is imposed.
--
--   This is the surjectivity half, in degree one, of a Shapiro-type comparison between level-constant cocycles of an open subgroup $S$ and level-constant cocycles of $G$ with values in the coinduced representation: every level-constant $1$-cocycle of $S$ is the restriction, evaluated at $1$, of a level-constant $1$-cocycle of $G$ on $\mathrm{CoInd}_S^G N$. It feeds the bijectivity statements [`groupCohomology.bijective_theta_coind`](thm.html#groupCohomology.bijective_theta_coind), [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and [`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen), which identify continuous cohomology of $G$ with that of its open subgroups.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_coind_cocycles1_isLevelConstant1_eval_one_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.exists_coind_cocycles1_isLevelConstant1_eval_one_eq {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) (b : groupCohomology.cocycles₁ N)
    (hb : groupCohomology.IsLevelConstant₁ (r.comp S.subtype) b) :
    ∃ c : groupCohomology.cocycles₁ (Rep.coind S.subtype N), groupCohomology.IsLevelConstant₁ r c ∧
      ∀ s : S, ((c (s : G) : Rep.coind S.subtype N) : G → N) 1 = b s := by sorry
