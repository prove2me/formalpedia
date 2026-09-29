-- Prove2me | Theorems.Thm_mme_CW_q6_common_halving_paired_oriented_power_Ctensor_mode_choice_certificate
-- name    : mme_CW_q6_common_halving_paired_oriented_power_Ctensor_mode_choice_certificate
-- status  : Open
-- author  : @marwahaha
-- created : 2026-08-27T11:53:07.047296+00:00
-- url     : https://prove2.me/theorems/44ef0626-0660-44dc-b894-b9829454b969
-- title:
--   Common-halving C-tensor certificate for the two oriented coupled half-powers
-- statement:
--   Let an exact primary $q=6$ hash family of length $2N$ use one common splitting of its coordinates into two halves of length $N$. Form the tensor product of the $N$-th power of the twice-cyclic orientation of the coupled constituent with the $N$-th power of its once-cyclic orientation. Then this paired oriented source has an induced mode-choice certificate to $A$ (not necessarily identically oriented) C-tensor stars. Every star has $H$ matrix-multiplication components, each of volume
--
--   $$6^{4G+2L}.$$
--
--   The certificate also exposes exact third-mode support. If the binary grade word of the first basis factor disagrees somewhere with the first-half mode-zero word of every family entry, or the second factor disagrees somewhere with the second-half mode-one word of every entry, then every third-mode slot annihilates that product basis vector.
--
--   This is the purely coupled-family core of the 121/211 branch. The separate source router and profile-mismatch theorems transport the literal Table-2 row pair into this source and verify the stated annihilation premise. Allowing heterogeneous stars avoids imposing a false common rectangular orientation on the two differently oriented half-powers.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), induced C-tensor construction on journal pp. 270-272; Ran Duan, Hongxun Wu, and Renfei Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, common-address splitting and rows 121/211 in Section 6.3/Table 2.

import Definitions.Def_CTensorOneHOneCertificate
import Definitions.Def_mme_CW_q6_common_paired_halving
import Definitions.Def_mme_CW_coupled_value
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_induced_mode_choice_certificate
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_permutation

open MME MME.TensorObj MME.DWZComponentRestriction Module TensorProduct

universe u

set_option autoImplicit false

theorem mme_CW_q6_common_halving_paired_oriented_power_Ctensor_mode_choice_certificate
    {K : Type u} [Field K]
    (N L G A H : ℕ)
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving) :
    let left :=
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (coupledObj K 6)).kronPow N
    let right :=
      (TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N
    let leftZBasis := kronPowModeBasis
      (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
        (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let rightZBasis := kronPowModeBasis
      (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
      ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex Equiv.ulift.symm) N
    let labelGrade : ULift.{u} (Fin 6 ⊕ Fin 6) → Fin 3 :=
      fun p ↦ Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
        (fun _ : Fin 6 ↦ (1 : Fin 3)) p.down
    ∃ star : Fin A → TensorObj K 3,
      ∃ cert : InducedModeChoiceCertificate
        (TensorObj.kron left right) (TensorObj.bigAdd star),
        (∀ (slot : Fin (cert.slotCount 2))
          (wX wY : PowIndex (ULift.{u} (Fin 6 ⊕ Fin 6)) N),
          ((∀ p : Fin A × Fin H,
              ∃ r : Fin N,
                labelGrade (PowIndex.get N wX r) ≠
                  (family.entry p).1 0
                    (halving.position (Sum.inl r))) ∨
            (∀ p : Fin A × Fin H,
              ∃ r : Fin N,
                labelGrade (PowIndex.get N wY r) ≠
                  (family.entry p).1 1
                    (halving.position (Sum.inr r)))) →
          cert.modeMap 2 slot
            (leftZBasis wX ⊗ₜ[K] rightZBasis wY) = 0) ∧
        Nonempty (∀ a : Fin A,
          CTensorOneHOneCertificate (star a) H
            (6 ^ (4 * G + 2 * L))) := by
  sorry
