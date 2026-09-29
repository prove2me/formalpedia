-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup
-- name    : groupCohomology.Kummer.exists_pow_eq_iff_of_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/b49933a8-bd38-5bcd-bc74-35c10cf94157
-- title:
--   Kummer descent criterion on the fixing subgroup of K
-- statement:
--   Let $k$ and $\Omega$ be fields with $\Omega$ a $k$-algebra that is Galois over $k$, let $K$ be an intermediate field of $\Omega/k$, let $p$ be a natural number, $a$ a unit of $K$ and $\alpha$ a unit of $\Omega$, and suppose that the image of $a$ under the structure map $K \to \Omega$ equals $\alpha^{p}$ in $\Omega$. Then $a$ is a $p$-th power in $K^{\times}$, i.e. there exists a unit $b$ of $K$ with $b^{p} = a$, if and only if there exists a unit $\zeta$ of $\Omega$ with $\zeta^{p} = 1$ such that for every element $\sigma$ of the fixing subgroup of $K$ inside $\mathrm{Gal}(\Omega/k)$ — that is, every $k$-algebra automorphism of $\Omega$ fixing $K$ pointwise — one has $(\sigma \cdot \zeta)/\zeta = (\sigma \cdot \alpha)/\alpha$, the right-hand side being the value `kummerCocycle α` at $\sigma$, defined as $(\sigma \cdot \alpha)/\alpha$ in $\Omega^{\times}$. The quantifier thus runs over the subgroup of $\mathrm{Gal}(\Omega/k)$ fixing $K$, and the automorphisms act on units of $\Omega$ through their action on $\Omega$.
--
--   This is the description of the kernel of the Kummer map, i.e. the statement that $a \in (K^{\times})^{p}$ precisely when the cocycle $\sigma \mapsto \sigma(\alpha)/\alpha$ with values in the $p$-th roots of unity is a coboundary, written with the Galois group of $\Omega/K$ presented concretely as the fixing subgroup of $K$ in $\mathrm{Gal}(\Omega/k)$. This form is the one used when $\Omega$ is an algebraic closure and $K$ a finite subextension, and it feeds the criterion [`groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one`](thm.html#groupCohomology.Kummer.exists_pow_eq_iff_forall_kummerCocycle_eq_one).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_pow_eq_iff_of_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_pow_eq_iff_of_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω] (K : IntermediateField k Ω)
    {p : ℕ} {a : Kˣ} {α : Ωˣ} (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (∃ b : Kˣ, b ^ p = a) ↔
      ∃ ζ : Ωˣ, ζ ^ p = 1 ∧ ∀ σ : K.fixingSubgroup,
        (σ : Ω ≃ₐ[k] Ω) • ζ / ζ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by sorry
