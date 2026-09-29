-- Prove2me | Theorems.Thm_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
-- name    : groupCohomology.smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:07.012926+00:00
-- url     : https://prove2.me/theorems/c5131f14-69f0-5209-86e7-c768c9b981a1
-- title:
--   Pairing χsmileκₐ is a level coboundary iff a is a norm
-- statement:
--   Let $K\subseteq\Omega$ be fields with $\Omega$ a Galois and algebraically closed extension of $K$, let $p$ be a prime, and let $r\colon(\Omega\simeq_K\Omega)\to(\overline{\mathbb{Q}}\simeq_{\mathbb{Q}}\overline{\mathbb{Q}})$ be a group homomorphism subject to two cofinality conditions: for every intermediate field $E$ of $\Omega/K$ finite over $K$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite over $\mathbb{Q}$ such that $r\sigma$ fixing $F$ pointwise forces $\sigma$ to fix $E$ pointwise, and conversely for every such $F$ there is such an $E$ with $\sigma$ fixing $E$ pointwise forcing $r\sigma$ to fix $F$ pointwise. Let $\chi\colon(\Omega\simeq_K\Omega)\to\mathbb{Z}$ satisfy the predicate `IsLevelConstant₁ r χ` and $p\mid\chi\sigma+\chi\tau-\chi(\sigma\tau)$ for all $\sigma,\tau$, so that $\chi$ reduces to a homomorphism modulo $p$; let $K_\chi$ be an intermediate field of $\Omega/K$, finite over $K$, whose fixing subgroup consists exactly of those $\sigma$ with $p\mid\chi\sigma$, and assume $\chi\sigma$ is not divisible by $p$ for at least one $\sigma$. Finally let $a\in K^\times$, $\alpha\in\Omega^\times$ with $a=\alpha^p$ in $\Omega$. Then the $2$-cochain sending $(\sigma,\tau)$ to the $\chi(\sigma)$-fold additive multiple of $\sigma$ applied to the $p$-th root of unity $\tau\alpha/\alpha$, viewed in the representation $\mathrm{Rep.ofMulDistribMulAction}$ on $\mu_p(\Omega)$, lies in `levelCoboundaries₂ r (Kummer.kummerRep K Ω p)` if and only if there exists $w\in K_\chi$ with $\mathrm{Algebra.norm}_K(w)=a$.
--
--   This is the local-symbol computation $(\chi,a)=0\iff a\in N_{K_\chi/K}(K_\chi^\times)$: the cup product of the additive character $\chi$ with the Kummer class of $a$ in the continuous second cohomology of $\mu_p$ vanishes exactly when $a$ is a norm from the cyclic extension cut out by $\chi$. It is used to exhibit a non-vanishing such class, via [`groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic`](thm.html#groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open CategoryTheory groupCohomology

theorem groupCohomology.smul_kummerCocycle_mem_levelCoboundaries2_iff_exists_norm_eq
    {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] [IsGalois K Ω] [IsAlgClosed Ω]
    (p : ℕ) [Fact p.Prime]
    (r : (Ω ≃ₐ[K] Ω) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K Ω, FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : Ω ≃ₐ[K] Ω, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K Ω, FiniteDimensional K E ∧
        ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (Ω ≃ₐ[K] Ω) → ℤ) (hχlc : IsLevelConstant₁ r χ)
    (hχ : ∀ σ τ : Ω ≃ₐ[K] Ω, (p : ℤ) ∣ χ σ + χ τ - χ (σ * τ))
    (Kχ : IntermediateField K Ω) [FiniteDimensional K Kχ]
    (hKχ : ∀ σ : Ω ≃ₐ[K] Ω, σ ∈ Kχ.fixingSubgroup ↔ (p : ℤ) ∣ χ σ)
    (hsurj : ∃ σ : Ω ≃ₐ[K] Ω, ¬ (p : ℤ) ∣ χ σ)
    (a : Kˣ) (α : Ωˣ) (hα : algebraMap K Ω (a : K) = (α : Ω) ^ p) :
    (fun g : (Ω ≃ₐ[K] Ω) × (Ω ≃ₐ[K] Ω) =>
        (χ g.1) • (Kummer.kummerRep K Ω p).ρ g.1 (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
      ∈ levelCoboundaries₂ r (Kummer.kummerRep K Ω p)
    ↔ ∃ w : Kχ, Algebra.norm K w = (a : K) := by sorry
