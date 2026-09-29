-- Prove2me | Theorems.Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff
-- name    : exists_finiteDimensional_comap_localGaloisToGlobal_iff
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/a95aa9c6-59fa-5a3a-b163-69f8091e9a23
-- title:
--   Global levels are cofinal among finite local levels
-- statement:
--   Let $q$ be a prime, let $\overline{\mathbb{Q}}_q$ denote `PadicAlgCl q` with its group $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$ of $\mathbb{Q}_q$-algebra automorphisms, and let $P$ be an arbitrary property of subgroups of that group which is inherited by subgroups, i.e. $P(U)$ and $V \le U$ imply $P(V)$. Write $r_q =$ [`localGaloisToGlobal q`](def/GaloisRep_CompletionBridge.html#L41) for the group homomorphism $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q) \to \mathrm{Gal}(\overline{\mathbb{Q}}/\mathbb{Q})$ obtained by viewing a $\mathbb{Q}_q$-automorphism of $\overline{\mathbb{Q}}_q$ as a $\mathbb{Q}$-automorphism and then restricting it along `AlgEquiv.restrictNormalHom` to the normal intermediate field `AlgebraicClosure ℚ`. The assertion is the equivalence of two existence statements: on the one hand, there is an intermediate field $F$ of $\overline{\mathbb{Q}}/\mathbb{Q}$, finite-dimensional over $\mathbb{Q}$, such that $P$ holds of the preimage $r_q^{-1}(\mathrm{Gal}(\overline{\mathbb{Q}}/F))$ of the pointwise fixing subgroup of $F$; on the other hand, there is an intermediate field $K$ of $\overline{\mathbb{Q}}_q/\mathbb{Q}_q$, finite-dimensional over $\mathbb{Q}_q$, such that $P$ holds of the pointwise fixing subgroup $\mathrm{Gal}(\overline{\mathbb{Q}}_q/K)$.
--
--   This packages the mutual cofinality of the two natural families of levels in $\mathrm{Gal}(\overline{\mathbb{Q}}_q/\mathbb{Q}_q)$: pull-backs of $\mathrm{Gal}(\overline{\mathbb{Q}}/F)$ for number fields $F$, and the open subgroups $\mathrm{Gal}(\overline{\mathbb{Q}}_q/K)$ for finite extensions $K/\mathbb{Q}_q$. It is used to convert conditions stated at global levels (smoothness of a vector, local constancy of a cochain) into conditions at finite local levels, and conversely.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_exists_finiteDimensional_comap_localGaloisToGlobal_iff.lean

import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
open scoped IntermediateField

theorem exists_finiteDimensional_comap_localGaloisToGlobal_iff
    (q : ℕ) [Fact q.Prime]
    (P : Subgroup (PadicAlgCl q ≃ₐ[ℚ_[q]] PadicAlgCl q) → Prop)
    (hP : ∀ U V, V ≤ U → P U → P V) :
    (∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧
        P (F.fixingSubgroup.comap (localGaloisToGlobal q))) ↔
      ∃ K : IntermediateField ℚ_[q] (PadicAlgCl q), FiniteDimensional ℚ_[q] K ∧
        P K.fixingSubgroup := by sorry
