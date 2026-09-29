-- Prove2me | solution 1 for mme_dwz_step1MixedModeEquiv_apply_arbitraryCoarseAddressModeBasis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:40:47.889959+00:00
-- url     : https://prove2.me/submissions/5eda0874-cfd2-4085-aa7c-e683cc708fce

import Definitions.Def_mme_dwz_step1_mixed_selected_full_map_data

open MME Module

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

open MME.DWZSourceAligned
open MME.DWZGlobalCorrelated

private theorem kronFinModePiBasis_apply_succ
    {K : Type u} [Field K] {d R : ℕ}
    (X : Fin (R + 1) → TensorObj K d) (i : Fin d)
    {Index : Fin (R + 1) → Type u}
    [∀ r, Fintype (Index r)] [∀ r, DecidableEq (Index r)]
    (b : ∀ r, Basis (Index r) K ((X r).V i))
    (word : ∀ r, Index r) :
    TensorObj.kronFinModePiBasis (R + 1) X i b word =
      (b 0 (word 0)) ⊗ₜ[K]
        TensorObj.kronFinModePiBasis R (fun r ↦ X r.succ) i
          (fun r ↦ b r.succ) (fun r ↦ word r.succ) := by
  let tailBasis := TensorObj.kronFinModePiBasis R
    (fun r ↦ X r.succ) i (fun r ↦ b r.succ)
  change (((b 0).tensorProduct tailBasis).reindex
    (Fin.consEquiv Index)) word = _
  rw [show (((b 0).tensorProduct tailBasis).reindex
      (Fin.consEquiv Index)) word =
      ((b 0).tensorProduct tailBasis) ((Fin.consEquiv Index).symm word) from
    Module.Basis.reindex_apply ((b 0).tensorProduct tailBasis)
      (Fin.consEquiv Index) word]
  change ((b 0).tensorProduct tailBasis)
      (word 0, fun r ↦ word r.succ) = _
  exact Module.Basis.tensorProduct_apply (b 0) tailBasis
    (word 0) (fun r ↦ word r.succ)

private theorem gradedAddressBlockModeEquiv_apply_kronFinModePiBasis
    {K : Type u} [Field K] {T : TensorObj K 3} {t R : ℕ}
    (G : T.TypeGrading t)
    (address address' : Fin 3 → Fin R → Fin t)
    (i : Fin 3) (hi : address i = address' i)
    {Index : Fin R → Type u}
    [∀ r, Fintype (Index r)] [∀ r, DecidableEq (Index r)]
    (b : ∀ r, Basis (Index r) K
      (((G.blockSubtensor (fun j ↦ address j r)).V i)))
    (b' : ∀ r, Basis (Index r) K
      (((G.blockSubtensor (fun j ↦ address' j r)).V i)))
    (word : ∀ r, Index r)
    (hfactor : ∀ r,
      LinearEquiv.ofEq
          (G.classOf i (address i r))
          (G.classOf i (address' i r))
          (by rw [congrFun hi r])
          (b r (word r)) =
        b' r (word r)) :
    CoupledCTensorPackaging.gradedAddressBlockModeEquiv
        G R address address' i hi
        (TensorObj.kronFinModePiBasis R
          (fun r ↦ G.blockSubtensor (fun j ↦ address j r)) i b word) =
      TensorObj.kronFinModePiBasis R
        (fun r ↦ G.blockSubtensor (fun j ↦ address' j r)) i b' word := by
  induction R with
  | zero =>
      rfl
  | succ R ih =>
      rw [kronFinModePiBasis_apply_succ
        (fun r ↦ G.blockSubtensor (fun j ↦ address j r)) i b word]
      rw [kronFinModePiBasis_apply_succ
        (fun r ↦ G.blockSubtensor (fun j ↦ address' j r)) i b' word]
      have htail := ih
        (address := fun j r ↦ address j r.succ)
        (address' := fun j r ↦ address' j r.succ)
        (hi := by
          funext r
          exact congrFun hi r.succ)
        (b := fun r ↦ b r.succ) (b' := fun r ↦ b' r.succ)
        (word := fun r ↦ word r.succ)
        (fun r ↦ hfactor r.succ)
      unfold CoupledCTensorPackaging.gradedAddressBlockModeEquiv
      calc
        _ =
            (LinearEquiv.ofEq
              (G.classOf i (address i 0))
              (G.classOf i (address' i 0))
              (by rw [congrFun hi 0])
              (b 0 (word 0))) ⊗ₜ[K]
            (CoupledCTensorPackaging.gradedAddressBlockModeEquiv G R
              (fun j r ↦ address j r.succ)
              (fun j r ↦ address' j r.succ) i (by
                funext r
                exact congrFun hi r.succ)
              (TensorObj.kronFinModePiBasis R
                (fun r ↦ G.blockSubtensor (fun j ↦ address j r.succ)) i
                (fun r ↦ b r.succ) (fun r ↦ word r.succ))) := by
              exact TensorProduct.congr_tmul _ _ _ _
        _ = _ := congrArg₂ (fun x y ↦ x ⊗ₜ[K] y) (hfactor 0) htail

theorem solution
    {K : Type u} [Field K] {N L n : ℕ}
    (reindex : Fin (N + 1) ≃ Fin L)
    (edge : Fin n → Fin (N + 1) → Fin 15)
    (competitor owner : Fin n) (i : Fin 3)
    (word : AddressModeWord
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i)) i) :
    step1MixedModeEquiv K reindex edge competitor owner i
        (arbitraryCoarseAddressModeBasis K
          (step1MixedAddress reindex edge competitor owner) i word) =
      coarseAddressModeBasis K
        (sourceWord reindex edge
          (step1MixedOwnerIndex competitor owner i)) i word := by
  apply gradedAddressBlockModeEquiv_apply_kronFinModePiBasis
    (cwSquareCanonicalGrading K 6)
    (step1MixedAddress reindex edge competitor owner)
    (coarseAddress
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i))) i rfl
    (fun r ↦ arbitraryCoarseComponentModeBasis K
      (fun j ↦ step1MixedAddress reindex edge competitor owner j r) i)
    (fun r ↦ canonicalComponentModeBasis K
      (sourceWord reindex edge
        (step1MixedOwnerIndex competitor owner i) r) i)
    word
  intro r
  rfl
