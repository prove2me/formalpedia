-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup
-- name    : groupCohomology.Kummer.kummerCocycle_mul_of_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/929728fb-dca9-5968-bcb1-7fd9621d06a7
-- title:
--   Kummer cocycle is multiplicative on Gal(Ω/K)
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra, let $K$ be an intermediate field of $\Omega/k$, and let $p$ be a natural number. Assume that every $\zeta \in \Omega$ with $\zeta^p = 1$ already lies in $K$. Let $a \in K$ and let $\alpha$ be a unit of $\Omega$ such that the image of $a$ under the structure map $K \to \Omega$ equals $\alpha^p$. Let $\sigma, \tau$ be $k$-algebra automorphisms of $\Omega$ lying in the fixing subgroup of $K$, i.e. acting as the identity on every element of $K$. Writing $\mathrm{kummerCocycle}\;\alpha\;\sigma$ for the unit $(\sigma \bullet \alpha)/\alpha$ of $\Omega$, the conclusion is the multiplicativity relation
--   $$\mathrm{kummerCocycle}\;\alpha\;(\sigma\tau) = (\mathrm{kummerCocycle}\;\alpha\;\sigma)\cdot(\mathrm{kummerCocycle}\;\alpha\;\tau)$$
--   in $\Omega^\times$. Thus, under the stated hypotheses, the restriction of the Kummer cocycle attached to $\alpha$ to the subgroup of automorphisms fixing $K$ is a group homomorphism into $\Omega^\times$.
--
--   This is the standard first step of Kummer theory: once the $p$-th roots of unity of $\Omega$ lie in $K$ and $\alpha^p$ is defined over $K$, the twisted cocycle $\sigma \mapsto \sigma(\alpha)/\alpha$ becomes an honest character of $\mathrm{Gal}(\Omega/K)$ with values in the $p$-th roots of unity. It feeds the computation of the index of $p$-th powers via [`groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom`](thm.html#groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom) and, through that, a dimension count for equivariant homomorphisms.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerCocycle_mul_of_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerCocycle_mul_of_mem_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α : Ωˣ} (hα : algebraMap K Ω a = (α : Ω) ^ p)
    {σ τ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) (hτ : τ ∈ K.fixingSubgroup) :
    kummerCocycle α (σ * τ) = kummerCocycle α σ * kummerCocycle α τ := by sorry
