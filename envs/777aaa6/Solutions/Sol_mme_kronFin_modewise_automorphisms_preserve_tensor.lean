-- Prove2me | solution 1 for mme_kronFin_modewise_automorphisms_preserve_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T09:48:58.686225+00:00
-- url     : https://prove2.me/submissions/87749994-3bdd-4d78-ba29-ad038b428e90

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_TypeGrading_kron

open MME MME.TensorObj PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

set_option linter.unusedVariables false in
private noncomputable def kronFinModeEquiv
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (n : ℕ) (T : Fin n → TensorObj K d)
      (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i) (i : Fin d),
      (TensorObj.kronFin n T).V i ≃ₗ[K]
        (TensorObj.kronFin n T).V i
  | 0, _, _, _ => LinearEquiv.refl K K
  | n + 1, T, E, i =>
      TensorProduct.congr (E 0 i)
        (kronFinModeEquiv n
          (fun r : Fin n ↦ T r.succ)
          (fun r j ↦ E r.succ j) i)

private theorem kronFinModeEquiv_preserves
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d)
    (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i)
    (hE : ∀ r,
      PiTensorProduct.map (fun i ↦ (E r i).toLinearMap) (T r).t =
        (T r).t) :
    PiTensorProduct.map
        (fun i ↦ (kronFinModeEquiv n T E i).toLinearMap)
        (TensorObj.kronFin n T).t =
      (TensorObj.kronFin n T).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (TensorObj.oneObj (K := K) (d := d)).t =
        (TensorObj.oneObj (K := K) (d := d)).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map (E 0 i).toLinearMap
            (kronFinModeEquiv n
              (fun r : Fin n ↦ T r.succ)
              (fun r j ↦ E r.succ j) i).toLinearMap)
          (interchange (T 0).t
            (TensorObj.kronFin n (fun r : Fin n ↦ T r.succ)).t) =
        interchange (T 0).t
          (TensorObj.kronFin n (fun r : Fin n ↦ T r.succ)).t
      rw [TensorObj.TypeGrading.kronMap_interchange, hE 0]
      rw [ih (fun r : Fin n ↦ T r.succ)
        (fun r j ↦ E r.succ j) (fun r ↦ hE r.succ)]

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d)
    (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i)
    (hE : ∀ r,
      PiTensorProduct.map (fun i ↦ (E r i).toLinearMap) (T r).t =
        (T r).t) :
    ∃ F : ∀ i,
        (TensorObj.kronFin n T).V i ≃ₗ[K]
          (TensorObj.kronFin n T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin n T).t =
        (TensorObj.kronFin n T).t := by
  exact ⟨fun i ↦ kronFinModeEquiv n T E i,
    kronFinModeEquiv_preserves T E hE⟩
