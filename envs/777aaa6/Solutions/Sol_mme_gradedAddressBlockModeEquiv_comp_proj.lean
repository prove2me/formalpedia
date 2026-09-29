-- Prove2me | solution 1 for mme_gradedAddressBlockModeEquiv_comp_proj
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-28T11:00:56.248089+00:00
-- url     : https://prove2.me/submissions/447f4a51-080b-4f5a-8ac0-2165a16046fb

import Definitions.Def_mme_coupled_Ctensor_outer_extraction_data

open MME Module
open CoupledCTensorPackaging

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000
set_option maxRecDepth 10000

theorem solution
    {K : Type u} [Field K]
    {t R : ℕ} {X : TensorObj K 3} (G0 : X.TypeGrading t)
    (address address' : Fin 3 → Fin R → Fin t)
    (i : Fin 3) (hi : address i = address' i) :
    (gradedAddressBlockModeEquiv
      G0 R address address' i hi).toLinearMap.comp
        (gradedAddressProj G0 R address i) =
      gradedAddressProj G0 R address' i := by
  induction R with
  | zero => rfl
  | succ R ih =>
      simp only [gradedAddressBlockModeEquiv, gradedAddressProj]
      apply TensorProduct.ext'
      intro x y
      change
        (LinearEquiv.ofEq
          (G0.classOf i (address i 0))
          (G0.classOf i (address' i 0)) _
          (G0.blockProj i (address i 0) x)) ⊗ₜ[K]
            (gradedAddressBlockModeEquiv G0 R
              (fun i' j ↦ address i' j.succ)
              (fun i' j ↦ address' i' j.succ) i _)
              (gradedAddressProj G0 R
                (fun i' j ↦ address i' j.succ) i y) =
          (G0.blockProj i (address' i 0) x) ⊗ₜ[K]
            gradedAddressProj G0 R
              (fun i' j ↦ address' i' j.succ) i y
      congr 1
      · have h0 : address i 0 = address' i 0 := congrFun hi 0
        apply Subtype.ext
        change
          ((G0.blockProj i (address i 0) x :
              G0.classOf i (address i 0)) : X.V i) =
            ((G0.blockProj i (address' i 0) x :
              G0.classOf i (address' i 0)) : X.V i)
        exact congrArg
          (fun r : Fin t ↦
            ((G0.blockProj i r x : G0.classOf i r) : X.V i)) h0
      · have htail :
            (fun j : Fin R ↦ address i j.succ) =
              (fun j : Fin R ↦ address' i j.succ) := by
          funext j
          exact congrFun hi j.succ
        have hih := ih
          (fun i' j ↦ address i' j.succ)
          (fun i' j ↦ address' i' j.succ) htail
        exact LinearMap.congr_fun hih y
