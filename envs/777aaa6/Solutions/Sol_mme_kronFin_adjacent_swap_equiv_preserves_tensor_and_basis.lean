-- Prove2me | solution 1 for mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:26:02.54759+00:00
-- url     : https://prove2.me/submissions/c963616f-79b4-46e6-bc4e-5230fafca671

import Theorems.Thm_mme_kronFin_adjacent_swap_preserves_tensor_and_basis
import Theorems.Thm_mme_finAdjacentSwapVector_eq_comp_swap
import Theorems.Thm_mme_kronFin_adjacent_swap_basis_word_semantics

open MME Module PiTensorProduct MME.TensorObj

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

private noncomputable def tensorEqModeEquiv
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (h : X = Y) (i : Fin d) : X.V i ≃ₗ[K] Y.V i := by
  subst h
  exact LinearEquiv.refl K _

private theorem tensorEqModeEquiv_map_tensor
    {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (h : X = Y) :
    PiTensorProduct.map
        (fun i ↦ (tensorEqModeEquiv h i).toLinearMap) X.t = Y.t := by
  subst h
  change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id) X.t = X.t
  rw [PiTensorProduct.map_id]
  rfl

private noncomputable def castFactorBasisFamily
    {K : Type u} [Field K] {d N : ℕ} (i : Fin d)
    {T U : Fin N → TensorObj K d} (hT : T = U)
    {indexT indexU : Fin N → Type u} (hI : indexT = indexU)
    (b : ∀ r, Basis (indexT r) K ((T r).V i)) :
    ∀ r, Basis (indexU r) K ((U r).V i) := by
  subst hT
  subst hI
  exact b

private def castIndexWord
    {N : ℕ} {indexT indexU : Fin N → Type u}
    (hI : indexT = indexU) (w : ∀ r, indexT r) : ∀ r, indexU r := by
  subst hI
  exact w

private theorem castFactorBasisFamily_apply_heq
    {K : Type u} [Field K] {d N : ℕ} (i : Fin d)
    {T U : Fin N → TensorObj K d} (hT : T = U)
    {indexT indexU : Fin N → Type u} (hI : indexT = indexU)
    (b : ∀ r, Basis (indexT r) K ((T r).V i)) (r : Fin N) :
    HEq (castFactorBasisFamily i hT hI b r) (b r) := by
  subst hT
  subst hI
  rfl

private theorem castIndexWord_apply_heq
    {N : ℕ} {indexT indexU : Fin N → Type u}
    (hI : indexT = indexU) (w : ∀ r, indexT r) (r : Fin N) :
    HEq (castIndexWord hI w r) (w r) := by
  subst hI
  rfl

private theorem tensorEqModeEquiv_kronFinModePiBasis
    {K : Type u} [Field K] {d N : ℕ} (i : Fin d)
    {T U : Fin N → TensorObj K d} (hT : T = U)
    {indexT indexU : Fin N → Type u} (hI : indexT = indexU)
    (b : ∀ r, Basis (indexT r) K ((T r).V i))
    (w : ∀ r, indexT r) :
    tensorEqModeEquiv
        (congrArg (TensorObj.kronFin (K := K) (d := d) N) hT) i
        (TensorObj.kronFinModePiBasis N T i b w) =
      TensorObj.kronFinModePiBasis N U i
        (castFactorBasisFamily i hT hI b) (castIndexWord hI w) := by
  subst hT
  subst hI
  rfl

theorem solution
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d) (j : Fin (n + 1)) :
    let s : Equiv.Perm (Fin (n + 2)) :=
      Equiv.swap j.castSucc j.succ
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (s r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (s r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (s r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (s r)) i (fun r ↦ b (s r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index s w) := by
  dsimp only
  let s : Equiv.Perm (Fin (n + 2)) :=
    Equiv.swap j.castSucc j.succ
  let Ts : Fin (n + 2) → TensorObj K d := fun r ↦ T (s r)
  let Tr : Fin (n + 2) → TensorObj K d :=
    kronFinAdjacentSwapFamily T j
  have hT : Ts = Tr := by
    exact (mme_finAdjacentSwapVector_eq_comp_swap T j).symm
  have hObj : TensorObj.kronFin (n + 2) Ts =
      TensorObj.kronFin (n + 2) Tr :=
    congrArg (TensorObj.kronFin (K := K) (d := d) (n + 2)) hT
  obtain ⟨Fswap, hSwap, hSwapBasis⟩ :=
    mme_kronFin_adjacent_swap_preserves_tensor_and_basis T j
  obtain ⟨hBasisSem, hWordSem⟩ :=
    mme_kronFin_adjacent_swap_basis_word_semantics T j
  let F : ∀ i : Fin d,
      (TensorObj.kronFin (n + 2) Ts).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i := fun i ↦
    (tensorEqModeEquiv hObj i).trans (Fswap i)
  refine ⟨F, ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (TensorObj.kronFin (n + 2) Ts).t = _
    have hF : (fun i ↦ (F i).toLinearMap) = fun i ↦
        (Fswap i).toLinearMap ∘ₗ
          (tensorEqModeEquiv hObj i).toLinearMap := by
      funext i
      rfl
    rw [hF, PiTensorProduct.map_comp, LinearMap.comp_apply,
      tensorEqModeEquiv_map_tensor hObj]
    exact hSwap
  · intro i index b w
    let indexS : Fin (n + 2) → Type u := fun r ↦ index (s r)
    let indexR : Fin (n + 2) → Type u :=
      kronFinAdjacentSwapIndex index j
    have hI : indexS = indexR := by
      exact (mme_finAdjacentSwapVector_eq_comp_swap index j).symm
    let bR := castFactorBasisFamily i hT hI
      (fun r ↦ b (s r))
    let wR := castIndexWord hI w
    have hbR : bR = kronFinAdjacentSwapBasis T j i b := by
      funext r
      apply eq_of_heq
      have hcast : HEq (bR r) (b (s r)) := by
        exact castFactorBasisFamily_apply_heq i hT hI
          (fun q ↦ b (s q)) r
      exact hcast.trans (hBasisSem i index b r).symm
    have hcast := tensorEqModeEquiv_kronFinModePiBasis i hT hI
      (fun r ↦ b (s r)) w
    have hout : kronFinAdjacentUnswapWord j wR =
        Equiv.piCongrLeft index s w := by
      funext r
      apply eq_of_heq
      have hu := hWordSem index wR r
      have hwR : ∀ q, HEq (wR q) (w q) := by
        intro q
        exact castIndexWord_apply_heq hI w q
      have hs : s.symm = s := by
        dsimp only [s]
        exact Equiv.swap_inv j.castSucc j.succ
      have hp : HEq ((Equiv.piCongrLeft index s w) r)
          (w (s r)) := by
        have hp0 : HEq ((Equiv.piCongrLeft index s w) r)
            (w (s.symm r)) := by
          rw [Equiv.piCongrLeft_apply]
          exact eqRec_heq _ _
        have harg : s.symm r = s r :=
          congrArg (fun e : Equiv.Perm (Fin (n + 2)) ↦ e r) hs
        have hp1 : HEq (w (s.symm r)) (w (s r)) := by
          cases harg
          rfl
        exact hp0.trans hp1
      exact hu.trans ((hwR (s r)).trans hp.symm)
    change (Fswap i)
        (tensorEqModeEquiv hObj i
          (TensorObj.kronFinModePiBasis (n + 2) Ts i
            (fun r ↦ b (s r)) w)) = _
    rw [hcast]
    change (Fswap i)
        (TensorObj.kronFinModePiBasis (n + 2) Tr i bR wR) = _
    rw [hbR, hSwapBasis i b wR, hout]
