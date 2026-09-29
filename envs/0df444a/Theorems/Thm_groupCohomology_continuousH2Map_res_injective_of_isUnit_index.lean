-- Prove2me | Theorems.Thm_groupCohomology_continuousH2Map_res_injective_of_isUnit_index
-- name    : groupCohomology.continuousH2Map_res_injective_of_isUnit_index
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/45ca6267-5cef-5733-bf18-0732fe56ae11
-- title:
--   Restriction on continuous H² is injective when [G:S] is invertible
-- statement:
--   Let $k$ be a commutative ring, $G$ a group, and $r \colon G \to \operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ a homomorphism into the group of $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Let $S \le G$ be a subgroup of finite index, and assume the openness-type hypothesis that there is an intermediate field $F_0$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, whose fixing subgroup has $r$-preimage contained in $S$; assume further that the image of the index $[G:S]$ in $k$ is a unit. Let $N$ be a $k$-linear representation of $G$. For a group $\Gamma$ with a homomorphism $\rho$ to $\operatorname{Aut}_{\mathbb{Q}}(\overline{\mathbb{Q}})$ and a representation $M$, `continuousH2 ρ M` is the quotient of the submodule `levelCocycles₂ ρ M` of $2$-cochains $\Gamma \times \Gamma \to M$ by the part of it lying in `levelCoboundaries₂ ρ M`. The assertion is that the map `continuousH2Map` attached to the inclusion $S \hookrightarrow G$ (with $r$ on $G$, its composite with the inclusion on $S$), to the identity of $N$ as a map $N \to \operatorname{Res}^G_S N$, and to the evident compatibilities, i.e. the restriction map $\mathrm{continuousH}^2(G,N) \to \mathrm{continuousH}^2(S, \operatorname{Res}^G_S N)$, is injective.
--
--   This is the standard fact that restriction to a subgroup of finite index is injective on $H^2$ once the index is invertible in the coefficient ring, here in the form adapted to the project's level-wise continuous $H^2$. It is used in the construction of liftings of projective or mod-$p$ representations, being cited in the results on restricting a class to a subgroup and in the local analysis of roots of unity.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_continuousH2Map_res_injective_of_isUnit_index.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_ContinuousH2Map

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u

open CategoryTheory

theorem groupCohomology.continuousH2Map_res_injective_of_isUnit_index {k G : Type u} [CommRing k] [Group G]
    (r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)) (S : Subgroup G) [S.FiniteIndex]
    (hS : ∃ F₀ : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F₀ ∧ F₀.fixingSubgroup.comap r ≤ S)
    (hu : IsUnit ((S.index : ℕ) : k)) (N : Rep.{u} k G) :
    Function.Injective (groupCohomology.continuousH2Map (rH := r) (rG := r.comp S.subtype) (A := N)
      (B := Rep.res S.subtype N) S.subtype (fun _ => rfl) LinearMap.id (fun _ _ => rfl)) := by sorry
