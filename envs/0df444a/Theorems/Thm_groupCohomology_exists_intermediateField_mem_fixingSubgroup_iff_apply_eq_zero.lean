-- Prove2me | Theorems.Thm_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
-- name    : groupCohomology.exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/b7ee7d09-7960-52d4-982f-3659cc1ccfef
-- title:
--   Degree-p Galois subextension cut out by an additive character
-- statement:
--   Let $K \subseteq \Omega$ be fields with $\Omega$ a $K$-algebra which is Galois over $K$, let $p$ be a prime, and let $r \colon \mathrm{Gal}(\Omega/K) = (\Omega \simeq_{\mathrm{alg}[K]} \Omega) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ be a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` over $\mathbb{Q}$. Assume $r$ has open levels in the following sense: for every intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ that is finite-dimensional over $\mathbb{Q}$ there is an intermediate field $E$ of $\Omega/K$, finite-dimensional over $K$, such that every $\sigma$ in the fixing subgroup of $E$ has $r\sigma$ in the fixing subgroup of $F$. Let $\chi \colon \mathrm{Gal}(\Omega/K) \to \mathbb{Z}/p$ be a function which is additive, $\chi(\sigma\tau) = \chi(\sigma) + \chi(\tau)$, which satisfies the predicate `IsLevelConstant₁ r χ` — a level-constancy condition relative to $r$, furnishing a finite extension $F$ of $\mathbb{Q}$ inside $\overline{\mathbb{Q}}$ such that $\chi(\sigma\tau) = \chi(\sigma)$ whenever $r\tau$ fixes $F$ pointwise — and which is not identically zero. Then there exists an intermediate field $E$ of $\Omega/K$ which is finite-dimensional over $K$, Galois over $K$, with $\dim_K E = p$, and such that for every $\sigma \in \mathrm{Gal}(\Omega/K)$ one has $\sigma$ in the fixing subgroup of $E$ if and only if $\chi(\sigma) = 0$.
--
--   This is the construction of the cyclic extension of degree $p$ attached to a non-zero additive character of a Galois group, here in the setting of a Galois group carrying a level map to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ with open levels. It is used in the Kummer-theoretic part of the continuous $H^2$ development, being cited by [`groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic`](thm.html#groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory

open groupCohomology

theorem groupCohomology.exists_intermediateField_mem_fixingSubgroup_iff_apply_eq_zero
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ZMod p) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχlc : IsLevelConstant₁ r χ) (hχ0 : ∃ σ, χ σ ≠ 0) :
    ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧ IsGalois K E ∧ Module.finrank K E = p ∧
      ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup ↔ χ σ = 0 := by sorry
