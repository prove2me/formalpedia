-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
-- name    : groupCohomology.Kummer.kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/f6676f5c-4237-5b40-ae95-dbd3d49e224c
-- title:
--   Kummer cocycle of a p-th root is μₚ-valued on Gal(Ω/K)
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra, let $K$ be an intermediate field of $\Omega/k$, and let $p$ be a natural number. Suppose given an element $a$ of $K$ and a unit $\alpha$ of $\Omega$ such that the image of $a$ under the structure map $K \to \Omega$ equals $\alpha^p$, so that $\alpha$ is a $p$-th root of $a$ in $\Omega$. Suppose further that $\sigma$ is a $k$-algebra automorphism of $\Omega$ lying in the fixing subgroup of $K$, i.e. $\sigma$ fixes every element of $K$ pointwise. Then the value at $\sigma$ of the Kummer cocycle attached to $\alpha$, namely the unit $\sigma \bullet \alpha / \alpha$ of $\Omega$ obtained from the natural action of the automorphism group on $\Omega^\times$, satisfies $(\sigma \bullet \alpha/\alpha)^p = 1$; that is, it is a $p$-th root of unity. No primality assumption on $p$ is made, and $a$ is not required to be a unit.
--
--   This is the standard observation underlying Kummer theory: the coboundary $\sigma \mapsto \sigma(\alpha)/\alpha$ of a $p$-th root of an element of $K$ takes values in $\mu_p$ once restricted to the subgroup of automorphisms fixing $K$, the relative form of the corresponding absolute statement for $K = k$. It feeds the comparison of the index of $p$-th powers with the cardinality of a level homomorphism group, and a computation of the rank of a space of continuous equivariant homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerCocycle_pow_eq_one_of_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerCocycle_pow_eq_one_of_mem_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    {a : K} {α : Ωˣ} (hα : algebraMap K Ω a = (α : Ω) ^ p)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCocycle α σ ^ p = 1 := by sorry
