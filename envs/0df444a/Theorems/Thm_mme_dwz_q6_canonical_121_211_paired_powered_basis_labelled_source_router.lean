-- Prove2me | Theorems.Thm_mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
-- name    : mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T11:19:24.000981+00:00
-- url     : https://prove2.me/theorems/e20ec5a8-1223-4ba5-bf65-b8db0f8e7eba
-- title:
--   Paired powered exact basis-labelled router for q=6 rows 121 and 211
-- statement:
--   The powered canonical row-121 and row-211 routers tensor together to an exact map from the paired full component source to the paired cyclically oriented coupled source. The map preserves the distinguished tensor and sends every product of named Z-word basis vectors by the same positionwise coordinate decoder on both factors. This is the labelled paired-source interface needed for allowed-word projector absorption in the asymmetric-hashing certificate.
-- source:
--   Duan, Wu, and Zhou, Faster Matrix Multiplication via Asymmetric Hashing, arXiv:2210.10173v5, Table 2 and Section 6.3; functoriality of tensor products.

import Definitions.Def_mme_dwz_q6_grade_one_coord_data
import Definitions.Def_mme_dwz_component_word_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_permutation
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false

theorem mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
    (K : Type u) [Field K] (n : ℕ) :
    ∃ coord : LiftedCoarsePair.{u} 6 1 ≃ (Fin 6 ⊕ Fin 6),
      (∀ p,
        p.leftGrade =
          Sum.elim (fun _ : Fin 6 ↦ (0 : Fin 3))
            (fun _ : Fin 6 ↦ (1 : Fin 3)) (coord p)) ∧
      ∃ maps : ∀ i : Fin 3,
          (TensorObj.kron
            ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)
            ((canonicalComponentBlock K (14 : Fin 15)).kronPow n)).V i →ₗ[K]
          (TensorObj.kron
            ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).kronPow n)
            ((TensorObj.permObj cyclicPerm
              (coupledObj K 6)).kronPow n)).V i,
        PiTensorProduct.map maps
            (TensorObj.kron
              ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)
              ((canonicalComponentBlock K (14 : Fin 15)).kronPow n)).t =
          (TensorObj.kron
            ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
              (coupledObj K 6)).kronPow n)
            ((TensorObj.permObj cyclicPerm
              (coupledObj K 6)).kronPow n)).t ∧
        ∀ (w13 w14 : PowIndex (LiftedCoarsePair.{u} 6 1) n),
          maps 2
              (kronPowModeBasis
                  (canonicalComponentBlock K (13 : Fin 15)) 2
                  (canonicalComponentZBasis K (13 : Fin 15)) n w13 ⊗ₜ[K]
                kronPowModeBasis
                  (canonicalComponentBlock K (14 : Fin 15)) 2
                  (canonicalComponentZBasis K (14 : Fin 15)) n w14) =
            kronPowModeBasis
                (TensorObj.permObj (cyclicPerm.trans cyclicPerm)
                  (coupledObj K 6)) 2
                ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                  Equiv.ulift.symm) n
                (PowIndex.ofFun n
                  (fun r ↦ ULift.up (coord (PowIndex.get n w13 r)))) ⊗ₜ[K]
              kronPowModeBasis
                (TensorObj.permObj cyclicPerm (coupledObj K 6)) 2
                ((Pi.basisFun K (Fin 6 ⊕ Fin 6)).reindex
                  Equiv.ulift.symm) n
                (PowIndex.ofFun n
                  (fun r ↦ ULift.up (coord (PowIndex.get n w14 r)))) := by
  sorry
