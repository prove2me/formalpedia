-- Prove2me | Theorems.Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
-- name    : groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/54d59aeb-fbe1-58a2-87f0-6e422fe2ca4f
-- title:
--   Kummer characters from p-torsion homomorphisms when μₚ⊂ K
-- statement:
--   Let $\Omega/k$ be a Galois extension of fields and let $K$ be an intermediate field of $\Omega/k$ that is finite-dimensional over $k$; write $U=K.\mathrm{fixingSubgroup}$ for the subgroup of $\Omega\simeq_{\mathrm{alg}[k]}\Omega$ fixing $K$ pointwise. Let $p$ be a nonzero natural number and assume that every $\zeta\in\Omega$ with $\zeta^p=1$ lies in $K$. Let $\chi:U\to\Omega^\times$ be a monoid homomorphism of groups of units such that $\chi(\sigma)^p=1$ for every $\sigma\in U$, and assume $\chi$ is locally trivial in the following sense: there is an intermediate field $L$ of $\Omega/k$, finite-dimensional over $k$, such that $\chi(\tau)=1$ for every $\tau\in U$ whose underlying $k$-automorphism of $\Omega$ lies in $L.\mathrm{fixingSubgroup}$. The conclusion is that there exist $a\in K^\times$ and $\alpha\in\Omega^\times$ with $\mathrm{algebraMap}_{K,\Omega}(a)=\alpha^p$ in $\Omega$ and such that for every $\sigma\in U$ one has $\chi(\sigma)=\mathrm{kummerCocycle}\,\alpha\,\sigma$, i.e. $\chi(\sigma)=(\sigma\cdot\alpha)/\alpha$ as units of $\Omega$.
--
--   This is the surjectivity half of Kummer theory in the situation where the $p$-th roots of unity of $\Omega$ already lie in $K$: every locally trivial $p$-torsion character of $\mathrm{Gal}(\Omega/K)$ arises from a $p$-th root of an element of $K^\times$. It is used in the computation of the index of $p$-th powers against continuous characters ([`groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom`](thm.html#groupCohomology.Kummer.natCard_quotient_range_pow_eq_natCard_levelHom)), in [`ValuationSubring.exists_kummer_generator_of_additive_inertia_character`](thm.html#ValuationSubring.exists_kummer_generator_of_additive_inertia_character), and in [`groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist`](thm.html#groupCohomology.finrank_continuousEquivariantHom_eq_finrank_invariants_linHom_dualTwist).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_Kummer_exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup.lean

import Mathlib
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

universe u v

open groupCohomology groupCohomology.Kummer

theorem groupCohomology.Kummer.exists_kummerCocycle_eq_of_monoidHom_fixingSubgroup
    {k Ω : Type} [Field k] [Field Ω] [Algebra k Ω] [IsGalois k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] {p : ℕ} [NeZero p]
    (hμ : ∀ ζ : Ω, ζ ^ p = 1 → ζ ∈ K)
    (χ : K.fixingSubgroup →* Ωˣ) (hχp : ∀ σ, χ σ ^ p = 1)
    (hlc : ∃ L : IntermediateField k Ω, FiniteDimensional k L ∧
      ∀ τ : K.fixingSubgroup, (τ : Ω ≃ₐ[k] Ω) ∈ L.fixingSubgroup → χ τ = 1) :
    ∃ (a : Kˣ) (α : Ωˣ), algebraMap K Ω (a : K) = (α : Ω) ^ p ∧
      ∀ σ : K.fixingSubgroup, χ σ = kummerCocycle α (σ : Ω ≃ₐ[k] Ω) := by sorry
