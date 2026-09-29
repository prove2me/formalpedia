-- Prove2me | solution 1 for mme_kronFin_modewise_basis_automorphisms_preserve_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T10:29:59.195354+00:00
-- url     : https://prove2.me/submissions/7a58f9c4-4835-474e-b222-5299efe8e04b

import Definitions.Def_mme_CW_2376_address_block
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_kronFin_mode_pi_basis

open MME MME.TensorObj PiTensorProduct Module

universe u

set_option autoImplicit false
set_option warningAsError true

set_option linter.unusedVariables false in
private noncomputable def kronFinModeLinearEquiv
    {K : Type u} [Field K] {d : ℕ} :
    ∀ (n : ℕ) (T : Fin n → TensorObj K d)
      (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i) (i : Fin d),
      (TensorObj.kronFin n T).V i ≃ₗ[K]
        (TensorObj.kronFin n T).V i
  | 0, _, _, _ => LinearEquiv.refl K K
  | n + 1, T, E, i =>
      TensorProduct.congr (E 0 i)
        (kronFinModeLinearEquiv
          n
          (fun r : Fin n ↦ T r.succ)
          (fun r j ↦ E r.succ j) i)

private theorem kronFinModeLinearEquiv_preserves_tensor
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d)
    (E : ∀ r i, (T r).V i ≃ₗ[K] (T r).V i)
    (hE : ∀ r,
      PiTensorProduct.map (fun i ↦ (E r i).toLinearMap) (T r).t =
        (T r).t) :
    PiTensorProduct.map
        (fun i ↦ (kronFinModeLinearEquiv n T E i).toLinearMap)
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
            (kronFinModeLinearEquiv
              n
              (fun r : Fin n ↦ T r.succ)
              (fun r j ↦ E r.succ j) i).toLinearMap)
          (interchange (T 0).t
            (TensorObj.kronFin n (fun r : Fin n ↦ T r.succ)).t) =
        interchange (T 0).t
          (TensorObj.kronFin n (fun r : Fin n ↦ T r.succ)).t
      rw [TensorObj.TypeGrading.kronMap_interchange, hE 0]
      rw [ih (fun r : Fin n ↦ T r.succ)
        (fun r j ↦ E r.succ j) (fun r ↦ hE r.succ)]

private theorem kronFinModeLinearEquiv_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (i : Fin d)
    {index : Fin n → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (E : ∀ r j, (T r).V j ≃ₗ[K] (T r).V j)
    (p : ∀ r, Equiv.Perm (index r))
    (hEb : ∀ r x, E r i (b r x) = b r (p r x))
    (w : ∀ r, index r) :
    kronFinModeLinearEquiv n T E i
        (TensorObj.kronFinModePiBasis n T i b w) =
      TensorObj.kronFinModePiBasis n T i b
        (fun r ↦ p r (w r)) := by
  induction n with
  | zero =>
      have hw : (fun r ↦ p r (w r)) = w := by
        funext r
        exact Fin.elim0 r
      rw [hw]
      rfl
  | succ n ih =>
      have hBasis (v : ∀ r, index r) :
          TensorObj.kronFinModePiBasis (n + 1) T i b v =
            (b 0 (v 0)) ⊗ₜ[K]
              (TensorObj.kronFinModePiBasis n
                (fun r : Fin n ↦ T r.succ) i
                (fun r ↦ b r.succ) (fun r ↦ v r.succ)) := by
        change (((b 0).tensorProduct
          (TensorObj.kronFinModePiBasis n
            (fun r : Fin n ↦ T r.succ) i
            (fun r ↦ b r.succ))).reindex (Fin.consEquiv index)) v = _
        rw [Module.Basis.reindex_apply, Fin.consEquiv_symm_apply,
          Module.Basis.tensorProduct_apply]
        rfl
      rw [hBasis w, hBasis (fun r ↦ p r (w r))]
      simp only [kronFinModeLinearEquiv]
      change TensorProduct.map (E 0 i).toLinearMap
          (kronFinModeLinearEquiv n
            (fun r : Fin n ↦ T r.succ)
            (fun r j ↦ E r.succ j) i).toLinearMap
          ((b 0 (w 0)) ⊗ₜ[K]
            (TensorObj.kronFinModePiBasis n
              (fun r : Fin n ↦ T r.succ) i
              (fun r ↦ b r.succ) (fun r ↦ w r.succ))) = _
      rw [TensorProduct.map_tmul]
      change (E 0 i) (b 0 (w 0)) ⊗ₜ[K]
          (kronFinModeLinearEquiv n
            (fun r : Fin n ↦ T r.succ)
            (fun r j ↦ E r.succ j) i)
            (TensorObj.kronFinModePiBasis n
              (fun r : Fin n ↦ T r.succ) i
              (fun r ↦ b r.succ) (fun r ↦ w r.succ)) = _
      rw [hEb 0]
      rw [ih (fun r : Fin n ↦ T r.succ)
        (fun r ↦ b r.succ) (fun r j ↦ E r.succ j)
        (fun r ↦ p r.succ) (fun r x ↦ hEb r.succ x)
        (fun r ↦ w r.succ)]

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin n → TensorObj K d) (i : Fin d)
    {index : Fin n → Type u}
    (b : ∀ r, Basis (index r) K ((T r).V i))
    (E : ∀ r j, (T r).V j ≃ₗ[K] (T r).V j)
    (p : ∀ r, Equiv.Perm (index r))
    (hEtensor : ∀ r,
      PiTensorProduct.map (fun j ↦ (E r j).toLinearMap) (T r).t =
        (T r).t)
    (hEb : ∀ r x, E r i (b r x) = b r (p r x)) :
    ∃ F : ∀ j,
        (TensorObj.kronFin n T).V j ≃ₗ[K]
          (TensorObj.kronFin n T).V j,
      PiTensorProduct.map (fun j ↦ (F j).toLinearMap)
          (TensorObj.kronFin n T).t =
        (TensorObj.kronFin n T).t ∧
      ∀ w : ∀ r, index r,
        F i (TensorObj.kronFinModePiBasis n T i b w) =
          TensorObj.kronFinModePiBasis n T i b
            (fun r ↦ p r (w r)) := by
  refine ⟨fun j ↦ kronFinModeLinearEquiv n T E j,
    kronFinModeLinearEquiv_preserves_tensor T E hEtensor, ?_⟩
  exact kronFinModeLinearEquiv_basis T i b E p hEb
