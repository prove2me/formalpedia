-- Prove2me | Theorems.Thm_mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
-- name    : mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-22T00:55:25.823513+00:00
-- url     : https://prove2.me/theorems/7c537aee-78be-443b-ac1e-ece9cd40435f
-- title:
--   Paired component projections annihilate mismatched third-mode basis words
-- statement:
--   Let $K$ be a field, let a primary $q=6$ coupled-address family have a common balanced halving, and choose one retained entry $p$. The third physical mode of the paired oriented source carries the first-half X coordinates and the second-half Y coordinates.
--
--   Write $b_X(w_X)$ and $b_Y(w_Y)$ for the standard tensor-product basis vectors of its two factors. Label a coordinate in the first copy of $\operatorname{Fin}(6)$ by grade $0$ and one in the second copy by grade $1$. If some coordinate of $w_X$ disagrees with the first-half X address of $p$, or some coordinate of $w_Y$ disagrees with its second-half Y address, then the literal component projection satisfies
--   $$P_{p,2}\bigl(b_X(w_X)\otimes b_Y(w_Y)\bigr)=0.$$
--   This statement holds without a paired-inducedness assumption. It supplies basis-word vanishing needed to compare component extraction maps with allowed-word projections of the source.
-- source:
--   Derived from the platform explicit coupled grading, common balanced halving, gradedAddressProj, and kronPowModeBasis definitions. The projection-on-a-different-grade argument follows the direct-sum decomposition used in the accepted explicit coupled four-block support proof. This is a source-word vanishing lemma, not an unconditional tensor extraction certificate.

import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_kron_pow_mode_word_basis
open MME MME.PairedOrientedPackaging MME.DWZComponentRestriction
open Module TensorProduct
universe u
set_option autoImplicit false

theorem mme_CW_q6_paired_oriented_componentProj_third_basis_vanishing
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) (p : Fin A × Fin H)
    (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N) :
    let labelGrade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun x => Sum.elim (fun _ : Fin 6 => (0 : Fin 3)) (fun _ : Fin 6 => 1) x.down
    ((∃ r, labelGrade (PowIndex.get N wX r) ≠
        (family.entry p).val 0 (halving.position (Sum.inl r))) ∨
      (∃ r, labelGrade (PowIndex.get N wY r) ≠
        (family.entry p).val 1 (halving.position (Sum.inr r)))) →
    componentProj (K := K) family halving p 2
      (kronPowModeBasis
          (TensorObj.permObj (cyclicPerm.trans cyclicPerm) (coupledObj K 6)) 2
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wX ⊗ₜ[K]
        kronPowModeBasis (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
          ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N wY) = 0 := by sorry
