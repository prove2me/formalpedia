-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin
-- name    : groupCohomology.Kummer.kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/44da67cb-4448-5b13-b3e8-3dea91706709
-- title:
--   Kummer cocycle is right-invariant under Gal(L/K(α))
-- statement:
--   Let $K$ and $L$ be fields with $L$ a $K$-algebra, let $\alpha$ be a unit of $L$, and let $\sigma,\tau$ be $K$-algebra automorphisms of $L$. For a unit $\alpha$ and an automorphism $\sigma$, the Kummer cocycle is the unit $\mathrm{kummerCocycle}\,\alpha\,\sigma = (\sigma \bullet \alpha)/\alpha$ of $L$, where $\bullet$ is the natural action of the automorphism group on $L^\times$. Assume that $\tau$ belongs to the fixing subgroup of the intermediate field $K(\alpha)$ obtained by adjoining to $K$ the singleton set $\{\alpha\}$ inside $L$, i.e.\ that $\tau$ fixes every element of $K(\alpha)$ pointwise. Then $\mathrm{kummerCocycle}\,\alpha\,(\sigma\tau) = \mathrm{kummerCocycle}\,\alpha\,\sigma$, the product $\sigma\tau$ being taken in the group of $K$-algebra automorphisms of $L$. No separability, normality or finiteness hypothesis on $L/K$ is imposed, and $\alpha$ need not be algebraic over $K$.
--
--   This is the statement that the Kummer cocycle $\sigma \mapsto \sigma(\alpha)/\alpha$ attached to a unit $\alpha$ is constant on right cosets of the subgroup fixing $K(\alpha)$, so that it factors through the coset space of that subgroup. It is used in the counting of continuous classes attached to a character, in [`groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot`](thm.html#groupCohomology.natCard_continuousClasses_ofChar_eq_natCard_units_quot).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerCocycle_mul_eq_of_mem_fixingSubgroup_adjoin
    {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L]
    (α : Lˣ) (σ τ : L ≃ₐ[K] L) (hτ : τ ∈ (IntermediateField.adjoin K {(α : L)}).fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ := by sorry
