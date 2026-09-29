-- Prove2me | Theorems.Thm_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
-- name    : groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/0ec9ab09-2e10-5abd-b71d-52c6fde964a0
-- title:
--   χ∪κₐ is not a level coboundary over a p-adic field
-- statement:
--   Let $q$ be a prime, let $K$ be an intermediate field of the algebraic closure `PadicAlgCl q` of $\mathbb{Q}_q$ over $\mathbb{Q}_q$ that is finite over $\mathbb{Q}_q$, and let $p$ be a prime. Let $r$ be a group homomorphism from $G_K = \mathrm{Gal}(\overline{\mathbb{Q}}_q/K)$, realised as the $K$-algebra automorphisms of `PadicAlgCl q`, to $\mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$, realised as the $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ`. Two cofinality hypotheses are imposed: for every finite extension $E/K$ inside `PadicAlgCl q` there is a finite extension $F/\mathbb{Q}$ inside `AlgebraicClosure ℚ` with $r^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F)) \subseteq \mathrm{Gal}(\overline{\mathbb{Q}}_q/E)$ (`hlevel`), and conversely for every such $F$ there is such an $E$ with $r(\mathrm{Gal}(\overline{\mathbb{Q}}_q/E)) \subseteq \mathrm{Gal}(\overline{\mathbb{Q}}/F)$ (`hopen`); here fixing subgroups are used throughout. Let $\chi : G_K \to \mathbb{Z}/p$ satisfy $\chi(\sigma\tau) = \chi(\sigma)+\chi(\tau)$, satisfy the predicate `IsLevelConstant₁ r χ` expressing constancy of $\chi$ along the levels determined by $r$, and be non-zero at some $\sigma$. Then there are a unit $a \in K^\times$, a unit $\alpha \in (\overline{\mathbb{Q}}_q)^\times$ and a proof $h_\alpha$ that the image of $a$ in $\overline{\mathbb{Q}}_q$ equals $\alpha^p$, such that the $2$-cochain $(\sigma,\tau) \mapsto \chi(\sigma)\cdot \sigma\big(\tau(\alpha)/\alpha\big)$ — written additively, with $\chi(\sigma)$ taken as its integer representative in $[0,p)$ acting on the $\mathbb{Z}$-representation `Kummer.kummerRep K (PadicAlgCl q) p` of $G_K$ on $\mu_p(\overline{\mathbb{Q}}_q)$, and with $\tau(\alpha)/\alpha$ the Kummer cocycle value `Kummer.kummerCocycleRoots hα` — does not lie in `levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p)`.
--
--   This is the non-degeneracy, on the character side, of the cup-product pairing $K^\times/(K^\times)^p \times \mathrm{Hom}(G_K,\mathbb{Z}/p) \to H^2(G_K,\mu_p)$ for a finite extension $K$ of $\mathbb{Q}_q$, in the level-theoretic formulation of continuous cochains used in this development. It feeds into [`groupCohomology.bijective_theta1_of_trivial_line_of_isOpen`](thm.html#groupCohomology.bijective_theta1_of_trivial_line_of_isOpen).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory

open groupCohomology

theorem groupCohomology.exists_smul_kummerCocycle_not_mem_levelCoboundaries2_of_padic
    (q : ℕ) [Fact q.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (p : ℕ) [Fact p.Prime]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (χ : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → ZMod p) (hχ : ∀ σ τ, χ (σ * τ) = χ σ + χ τ)
    (hχlc : IsLevelConstant₁ r χ) (hχ0 : ∃ σ, χ σ ≠ 0) :
    ∃ (a : (↥K)ˣ) (α : (PadicAlgCl q)ˣ) (hα : algebraMap K (PadicAlgCl q) (a : K) = (α : PadicAlgCl q) ^ p),
      (fun g : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) =>
          ((χ g.1).val : ℤ) • (Kummer.kummerRep K (PadicAlgCl q) p).ρ g.1
            (Additive.ofMul (Kummer.kummerCocycleRoots hα g.2)))
        ∉ levelCoboundaries₂ r (Kummer.kummerRep K (PadicAlgCl q) p) := by sorry
