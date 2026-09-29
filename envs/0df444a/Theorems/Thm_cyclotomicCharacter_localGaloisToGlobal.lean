-- Prove2me | Theorems.Thm_cyclotomicCharacter_localGaloisToGlobal
-- name    : cyclotomicCharacter_localGaloisToGlobal
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:31:06.414831+00:00
-- url     : https://prove2.me/theorems/eb864647-3fca-5b3b-88a0-35f6245e9155
-- title:
--   Cyclotomic characters agree under restriction to ℚ̄
-- statement:
--   Let $p$ be a prime and let $\sigma$ be an automorphism of the field `PadicAlgCl p` as a $\mathbb{Q}_p$-algebra. Write [`localGaloisToGlobal p`](def/GaloisRep_CompletionBridge.html#L41) for the monoid homomorphism from $\mathbb{Q}_p$-algebra automorphisms of `PadicAlgCl p` to $\mathbb{Q}$-algebra automorphisms of `AlgebraicClosure ℚ` obtained by first restricting scalars from $\mathbb{Q}_p$ to $\mathbb{Q}$ and then applying `AlgEquiv.restrictNormalHom`, i.e. restricting the resulting $\mathbb{Q}$-algebra automorphism to the normal subextension `AlgebraicClosure ℚ` of `PadicAlgCl p` determined by the fixed embedding [`padicEmbedding p`](def/GaloisRep_CompletionBridge.html#L17). The assertion is an equality in $\mathbb{Z}_p^{\times}$: the $p$-adic cyclotomic character of `AlgebraicClosure ℚ` evaluated at the ring isomorphism underlying [`localGaloisToGlobal p σ`](def/GaloisRep_CompletionBridge.html#L41) equals the $p$-adic cyclotomic character of `PadicAlgCl p` evaluated at the ring isomorphism underlying $\sigma$. Both characters are Mathlib's `cyclotomicCharacter`, available because each field contains enough $p^n$-th roots of unity for every $n$.
--
--   This is the compatibility of the global and local $p$-adic cyclotomic characters along the chosen embedding $\overline{\mathbb Q}\hookrightarrow\overline{\mathbb Q}_p$, and it allows the two spellings of $\chi_p$ used in the project (on $\overline{\mathbb Q}$ via restriction, and directly on $\overline{\mathbb Q}_p$) to be interchanged. It is used in [`PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul`](thm.html#PadicComplex.eq_zero_of_forall_mem_fixingSubgroup_smul_eq_cyclotomicCharacter_zpow_mul).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_cyclotomicCharacter_localGaloisToGlobal.lean

import Mathlib
import Definitions.Def_GaloisRep_CompletionBridge

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem cyclotomicCharacter_localGaloisToGlobal (p : ℕ) [Fact p.Prime]
    (σ : PadicAlgCl p ≃ₐ[ℚ_[p]] PadicAlgCl p) :
    cyclotomicCharacter (AlgebraicClosure ℚ) p (localGaloisToGlobal p σ).toRingEquiv =
      cyclotomicCharacter (PadicAlgCl p) p σ.toRingEquiv := by sorry
