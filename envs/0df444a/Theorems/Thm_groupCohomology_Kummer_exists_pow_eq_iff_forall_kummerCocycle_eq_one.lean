-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one
-- name    : groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/ebb24a69-b71d-54a1-97ac-00aceda57ec2
-- title:
--   Triviality of the Kummer cocycle when μₚ⊆ K
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra which is Galois over $k$, and let $K$ be an intermediate field of $\Omega/k$. Let $p$ be a natural number, and assume the hypothesis $h\mu$: every $\zeta\in\Omega$ with $\zeta^{p}=1$ already lies in $K$. Let $a$ be a unit of $K$ and $\alpha$ a unit of $\Omega$ such that the image of $a$ under the structure map $K\to\Omega$ equals $\alpha^{p}$. The assertion is an equivalence: there exists a unit $b$ of $K$ with $b^{p}=a$ if and only if, for every $\sigma$ in the fixing subgroup of $K$ inside $\mathrm{Gal}(\Omega/k)$ — that is, for every $k$-algebra automorphism of $\Omega$ fixing $K$ pointwise — the Kummer cocycle `kummerCocycle` of $\alpha$ at $\sigma$, defined as the unit $(\sigma\bullet\alpha)/\alpha$ of $\Omega$, is equal to $1$; equivalently $\sigma(\alpha)=\alpha$ for all such $\sigma$. No primality or positivity assumption is made on $p$.
--
--   This is the computation of the kernel of the Kummer map in the case where the $p$-th roots of unity of $\Omega$ are contained in $K$: then $a$ is a $p$-th power in $K^{\times}$ precisely when the cocycle $\sigma\mapsto\sigma(\alpha)/\alpha$ attached to a chosen $p$-th root $\alpha$ is identically trivial. It is used in the counting of the quotient of $K^\times$ by $p$-th powers against the group of level homomorphisms, and in the comparison of dimensions of spaces of continuous equivariant homomorphisms with invariants of a twisted dual.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_pow_eq_iff_forall_kummerCocycle_eq_one.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔ ∀ σ : K.fixingSubgroup, kummerCocycle α (σ : Ω ≃ₐ[k] Ω) = 1 := by sorry
