-- Prove2me | Theorems.Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
-- name    : groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/3515b452-101d-56b6-ae86-0471490f16f5
-- title:
--   Degree-two Shapiro injectivity for level coboundaries
-- statement:
--   Let $k$ be a commutative ring and $G$ a group (both in the same universe), let $r \colon G \to \mathrm{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ be a group homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`, and let $S \le G$ be a subgroup subject to the hypothesis that there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup has $r$-preimage contained in $S$. Let $N$ be a $k$-linear representation of $S$, and let $c \colon G \times G \to$ `Rep.coind S.subtype N` be a $2$-cochain valued in the representation of $G$ coinduced from $N$ along the inclusion $S \hookrightarrow G$, whose underlying object consists of functions $G \to N$. Assume $c$ lies in [`groupCohomology.levelCocycles₂ r (Rep.coind S.subtype N)`](def/GroupCohomology_ContinuousH2.html#L85), and that the $2$-cochain of $S$ with values in $N$ given by $(s,s') \mapsto c(s,s')(1)$, evaluation of $c$ on pairs from $S$ at the identity of $G$, lies in [`groupCohomology.levelCoboundaries₂ (r.comp S.subtype) N`](def/GroupCohomology_ContinuousH2.html#L92), the level coboundaries for the restriction of $r$ to $S$. The conclusion is that $c$ itself lies in [`groupCohomology.levelCoboundaries₂ r (Rep.coind S.subtype N)`](def/GroupCohomology_ContinuousH2.html#L92).
--
--   This is the injectivity half, in degree two, of Shapiro's lemma for the level (continuity) variant of group cohomology: the Shapiro map induced by evaluation at $1$ does not lose information modulo level coboundaries. It feeds the proofs that the comparison maps [`groupCohomology.bijective_theta_coind`](thm.html#groupCohomology.bijective_theta_coind), [`groupCohomology.bijective_theta_dualTwist_of_res`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res) and [`groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen`](thm.html#groupCohomology.bijective_theta_dualTwist_of_res_of_isOpen) are bijective.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_LevelSubgroup

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.coind_mem_levelCoboundaries2_of_eval_one_mem_levelCoboundaries2 {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G)
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (N : Rep.{u} k S) (c : G × G → Rep.coind S.subtype N)
    (hc : c ∈ groupCohomology.levelCocycles₂ r (Rep.coind S.subtype N))
    (h : (fun p : S × S => ((c ((p.1 : G), (p.2 : G)) : Rep.coind S.subtype N) : G → N) 1)
      ∈ groupCohomology.levelCoboundaries₂ (r.comp S.subtype) N) :
    c ∈ groupCohomology.levelCoboundaries₂ r (Rep.coind S.subtype N) := by sorry
