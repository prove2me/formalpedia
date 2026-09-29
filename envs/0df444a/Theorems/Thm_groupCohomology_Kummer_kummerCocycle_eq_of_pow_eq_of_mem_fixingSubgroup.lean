-- Prove2me | Theorems.Thm_groupCohomology_Kummer_kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup
-- name    : groupCohomology.Kummer.kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/338f4a77-c250-505f-8f65-58351353b90d
-- title:
--   Independence of the Kummer cocycle of the chosen p-th root
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra, let $K$ be an intermediate field of $\Omega/k$, and let $p$ be a natural number (neither assumed prime nor assumed nonzero). Suppose that every $\zeta \in \Omega$ with $\zeta^p = 1$ lies in $K$. Let $a$ be an element of $K$ and let $\alpha, \beta$ be units of $\Omega$ whose $p$-th powers both equal the image of $a$ under the structure map $K \to \Omega$, i.e. $\mathrm{algebraMap}\,K\,\Omega\,a = \alpha^p = \beta^p$ in $\Omega$. Let $\sigma$ be a $k$-algebra automorphism of $\Omega$ lying in the fixing subgroup of $K$, that is, $\sigma$ fixes every element of $K$. Then the values at $\sigma$ of the Kummer cocycles attached to $\alpha$ and to $\beta$ agree: with $\mathrm{kummerCocycle}\,\alpha\,\sigma$ defined as the unit $(\sigma \bullet \alpha)/\alpha$ of $\Omega$, one has $(\sigma \bullet \alpha)/\alpha = (\sigma \bullet \beta)/\beta$.
--
--   This is the well-definedness step of Kummer theory in the presence of the $p$-th roots of unity: when $\mu_p \subset K$, the Kummer character $\sigma \mapsto \sigma(\alpha)/\alpha$ on the group fixing $K$ depends only on $a$ and not on the choice of $p$-th root $\alpha$ of $a$. It is used in the computation of the cardinality of the quotient of $K^\times$ by $p$-th powers in terms of the relevant group of homomorphisms, [`groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom`](thm.html#groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.kummerCocycle_eq_of_pow_eq_of_mem_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] (K : IntermediateField k Ω) {p : ℕ}
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K) {a : K} {α β : Ωˣ}
    (hα : algebraMap K Ω a = (α : Ω) ^ p) (hβ : algebraMap K Ω a = (β : Ω) ^ p)
    {σ : Ω ≃ₐ[k] Ω} (hσ : σ ∈ K.fixingSubgroup) :
    kummerCocycle α σ = kummerCocycle β σ := by sorry
