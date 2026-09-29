-- Prove2me | solution 1 for mme_dwz_q6_canonical_121_211_paired_powered_basis_labelled_source_router
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T11:21:13.11916+00:00
-- url     : https://prove2.me/submissions/f5ef0a37-ddce-4061-9083-77af006b83ec

import Theorems.Thm_mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj MME.DWZComponentRestriction
  PiTensorProduct TensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

theorem solution
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
  obtain ⟨coord, hcoord, ⟨f13, hf13, hf13Z⟩,
      ⟨f14, hf14, hf14Z⟩⟩ :=
    mme_dwz_q6_canonical_121_211_powered_basis_labelled_source_routers K n
  let maps : ∀ i : Fin 3,
      (TensorObj.kron
        ((canonicalComponentBlock K (13 : Fin 15)).kronPow n)
        ((canonicalComponentBlock K (14 : Fin 15)).kronPow n)).V i →ₗ[K]
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow n)
        ((TensorObj.permObj cyclicPerm
          (coupledObj K 6)).kronPow n)).V i :=
    fun i ↦ TensorProduct.map (f13 i) (f14 i)
  refine ⟨coord, hcoord, maps, ?_, ?_⟩
  · change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (f13 i) (f14 i))
        (interchange
          ((canonicalComponentBlock K (13 : Fin 15)).kronPow n).t
          ((canonicalComponentBlock K (14 : Fin 15)).kronPow n).t) =
      interchange
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow n).t
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow n).t
    rw [TensorObj.TypeGrading.kronMap_interchange, hf13, hf14]
  · intro w13 w14
    change TensorProduct.map (f13 2) (f14 2) (_ ⊗ₜ[K] _) = _
    rw [TensorProduct.map_tmul, hf13Z, hf14Z]

