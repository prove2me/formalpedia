-- Prove2me | Theorems.Thm_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
-- name    : groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.755445+00:00
-- url     : https://prove2.me/theorems/a97c4b2e-8691-570c-9179-684146ab49af
-- title:
--   Level 2-cocycles in μₚ bound over an unramified layer
-- statement:
--   Let $q$ and $p$ be primes, let $\Omega =$ `PadicAlgCl q` be the fixed algebraic closure of $\mathbb{Q}_q$, and let $K$ be an intermediate field of $\Omega/\mathbb{Q}_q$ that is finite-dimensional over $\mathbb{Q}_q$. Let $r \colon (\Omega \simeq_{\mathrm{alg}[K]} \Omega) \to (\overline{\mathbb{Q}} \simeq_{\mathrm{alg}[\mathbb{Q}]} \overline{\mathbb{Q}})$ be a group homomorphism into the automorphism group of `AlgebraicClosure ℚ` subject to two cofinality hypotheses: for every intermediate field $E$ of $\Omega/K$ finite-dimensional over $K$ there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$ finite-dimensional over $\mathbb{Q}$ such that every $\sigma$ with $r\sigma$ in the fixing subgroup of $F$ lies in the fixing subgroup of $E$ (`hlevel`), and conversely for every such $F$ there is such an $E$ with $\sigma$ in the fixing subgroup of $E$ implying $r\sigma$ in the fixing subgroup of $F$ (`hopen`). Let $c$ be a function on pairs of $K$-automorphisms of $\Omega$ with values in `Kummer.kummerRep K Ω p`, i.e. in the group $\mu_p(\Omega) =$ `rootsOfUnity p Ω` viewed additively as a $\mathbb{Z}$-linear representation of $\Omega \simeq_{\mathrm{alg}[K]} \Omega$ via the multiplicative action, and assume $c \in$ `levelCocycles₂ r (Kummer.kummerRep K Ω p)`. Then there is $N > 0$ such that, writing $L_N =$ `IntermediateField.adjoin K {ζ | ζ ^ (q ^ N - 1) = 1}` and $j$ for the inclusion $(\Omega \simeq_{\mathrm{alg}[L_N]} \Omega) \to (\Omega \simeq_{\mathrm{alg}[K]} \Omega)$ obtained from `IntermediateField.fixingSubgroupEquiv` and the inclusion of the fixing subgroup, the restriction $c \circ (j \times j)$ lies in `levelCoboundaries₂ (r.comp j) (Kummer.kummerRep L_N Ω p)`.
--
--   This is the $\mu_p$-coefficient form of the statement that a continuous $2$-cocycle of the absolute Galois group of a $q$-adic field becomes a coboundary after restriction to a finite unramified layer $K(\mu_{q^N-1})$, with continuity encoded through the level map $r$. It is used in the construction of Galois cohomology classes with roots-of-unity coefficients, and is cited by [`groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup`](thm.html#groupCohomology.exists_restrict_rootsOfUnity_mem_levelCoboundaries2_trivial_of_fixingSubgroup).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_groupCohomology_exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic.lean

import Mathlib
import Definitions.Def_GroupCohomology_ContinuousH2
import Definitions.Def_GroupCohomology_Kummer

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory groupCohomology IntermediateField

theorem groupCohomology.exists_restrict_adjoin_rootsOfUnity_mem_levelCoboundaries2_kummerRep_of_padic
    (q : ℕ) [Fact q.Prime] (p : ℕ) [Fact p.Prime]
    (K : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] K]
    (r : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ))
    (hlevel : ∀ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E →
      ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, r σ ∈ F.fixingSubgroup → σ ∈ E.fixingSubgroup)
    (hopen : ∀ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F →
      ∃ E : IntermediateField K (PadicAlgCl q), FiniteDimensional K E ∧
        ∀ σ : PadicAlgCl q ≃ₐ[K] PadicAlgCl q, σ ∈ E.fixingSubgroup → r σ ∈ F.fixingSubgroup)
    (c : (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) × (PadicAlgCl q ≃ₐ[K] PadicAlgCl q) → Kummer.kummerRep K (PadicAlgCl q) p)
    (hc : c ∈ levelCocycles₂ r (Kummer.kummerRep K (PadicAlgCl q) p)) :
    ∃ (N : ℕ) (_ : 0 < N),
      (fun g : (PadicAlgCl q ≃ₐ[IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}] PadicAlgCl q)
              × (PadicAlgCl q ≃ₐ[IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}] PadicAlgCl q) =>
          c (((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom) g.1,
             ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom) g.2))
        ∈ levelCoboundaries₂
            (r.comp ((IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}).fixingSubgroup.subtype.comp
                (IntermediateField.fixingSubgroupEquiv (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1})).symm.toMonoidHom))
            (Kummer.kummerRep (IntermediateField.adjoin K {ζ : PadicAlgCl q | ζ ^ (q ^ N - 1) = 1}) (PadicAlgCl q) p) := by sorry
