-- Prove2me | solution 1 for mme_kronFin_perm_preserves_tensor_and_basis
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-26T20:33:43.181973+00:00
-- url     : https://prove2.me/submissions/7f5716af-41a4-4ee3-997e-1e71d64dbb64

import Theorems.Thm_mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis
import Mathlib.GroupTheory.Perm.Sign

open MME Module PiTensorProduct

universe u v

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.TensorObj

private def ExactPermutationProperty
    (K : Type u) [Field K] (d n : ℕ)
    (e : Equiv.Perm (Fin (n + 2))) : Prop :=
  ∀ T : Fin (n + 2) → TensorObj K d,
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (e r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (e r)) i (fun r ↦ b (e r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index e w)

private theorem piCongrLeft_apply_heq
    {α : Sort v} (index : α → Type u) (e : Equiv.Perm α)
    (w : ∀ r, index (e r)) (r : α) :
    HEq ((Equiv.piCongrLeft index e w) r) (w (e.symm r)) := by
  rw [Equiv.piCongrLeft_apply]
  exact eqRec_heq _ _

private theorem piCongrLeft_mul
    {α : Type v} (index : α → Type u) (a b : Equiv.Perm α)
    (w : ∀ r, index ((a * b) r)) :
    Equiv.piCongrLeft index a
        (Equiv.piCongrLeft (fun r ↦ index (a r)) b w) =
      Equiv.piCongrLeft index (a * b) w := by
  funext r
  apply eq_of_heq
  have h1 := piCongrLeft_apply_heq index a
    (Equiv.piCongrLeft (fun q ↦ index (a q)) b w) r
  have h2 := piCongrLeft_apply_heq (fun q ↦ index (a q)) b w (a.symm r)
  have h3 := piCongrLeft_apply_heq index (a * b) w r
  have harg : b.symm (a.symm r) = (a * b).symm r := by
    rfl
  have hmid : HEq (w (b.symm (a.symm r)))
      (w ((a * b).symm r)) := by
    cases harg
    rfl
  exact (h1.trans h2).trans (hmid.trans h3.symm)

private theorem exactPermutationProperty_one
    {K : Type u} [Field K] {d n : ℕ} :
    ExactPermutationProperty K d n 1 := by
  intro T
  let F : ∀ i : Fin d,
      (TensorObj.kronFin (n + 2)
        (fun r ↦ T ((1 : Equiv.Perm (Fin (n + 2))) r))).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i := fun i ↦
    LinearEquiv.refl K _
  refine ⟨F, ?_, ?_⟩
  · change PiTensorProduct.map (fun _ : Fin d ↦ LinearMap.id)
      (TensorObj.kronFin (n + 2) T).t = _
    rw [PiTensorProduct.map_id]
    rfl
  · intro i index b w
    change TensorObj.kronFinModePiBasis (n + 2) T i b w = _
    congr 1

private theorem exactPermutationProperty_mul
    {K : Type u} [Field K] {d n : ℕ}
    (a b : Equiv.Perm (Fin (n + 2)))
    (ha : ExactPermutationProperty K d n a)
    (hb : ExactPermutationProperty K d n b) :
    ExactPermutationProperty K d n (a * b) := by
  intro T
  obtain ⟨Fa, hTa, hBa⟩ := ha T
  obtain ⟨Fb, hTb, hBb⟩ := hb (fun r ↦ T (a r))
  let F : ∀ i : Fin d,
      (TensorObj.kronFin (n + 2) (fun r ↦ T ((a * b) r))).V i ≃ₗ[K]
        (TensorObj.kronFin (n + 2) T).V i := fun i ↦
    (Fb i).trans (Fa i)
  refine ⟨F, ?_, ?_⟩
  · have hF : (fun i ↦ (F i).toLinearMap) = fun i ↦
        (Fa i).toLinearMap ∘ₗ (Fb i).toLinearMap := by
      funext i
      rfl
    change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (TensorObj.kronFin (n + 2) (fun r ↦ T ((a * b) r))).t = _
    rw [hF]
    simp only [Equiv.Perm.mul_apply]
    let src := (TensorObj.kronFin (n + 2)
      (fun r ↦ T (a (b r)))).t
    have hcomp := congrArg (fun L ↦ L src)
      (PiTensorProduct.map_comp
        (fun i ↦ (Fa i).toLinearMap) (fun i ↦ (Fb i).toLinearMap))
    calc
      PiTensorProduct.map
          (fun i ↦ (Fa i).toLinearMap ∘ₗ (Fb i).toLinearMap) src =
          PiTensorProduct.map (fun i ↦ (Fa i).toLinearMap)
            (PiTensorProduct.map (fun i ↦ (Fb i).toLinearMap) src) := by
        simpa only [LinearMap.comp_apply] using hcomp
      _ = PiTensorProduct.map (fun i ↦ (Fa i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (a r))).t := by
        exact congrArg (PiTensorProduct.map (fun i ↦ (Fa i).toLinearMap)) hTb
      _ = (TensorObj.kronFin (n + 2) T).t := hTa
  · intro i index basis w
    let indexA : Fin (n + 2) → Type u := fun r ↦ index (a r)
    let basisA : ∀ r, Basis (indexA r) K ((T (a r)).V i) :=
      fun r ↦ basis (a r)
    have hFirst := hBb i indexA basisA w
    have hSecond := hBa i index basis
      (Equiv.piCongrLeft indexA b w)
    have hPi := piCongrLeft_mul index a b w
    simp only [Equiv.Perm.mul_apply]
    change (Fa i) ((Fb i)
      (TensorObj.kronFinModePiBasis (n + 2)
        (fun r ↦ T (a (b r))) i
        (fun r ↦ basis (a (b r))) w)) = _
    rw [hFirst, hSecond]
    exact congrArg (TensorObj.kronFinModePiBasis (n + 2) T i basis) hPi

/-- Every permutation of at least two heterogeneous Kronecker factors is
realized by literal tensor-preserving mode equivalences, with its exact action
on all dependent product bases. -/
theorem mme_kronFin_perm_preserves_tensor_and_basis
    {K : Type u} [Field K] {d n : ℕ}
    (T : Fin (n + 2) → TensorObj K d)
    (e : Equiv.Perm (Fin (n + 2))) :
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (e r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (e r)) i (fun r ↦ b (e r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index e w) := by
  let S : Set (Equiv.Perm (Fin (n + 2))) :=
    Set.range (fun j : Fin (n + 1) ↦ Equiv.swap j.castSucc j.succ)
  have he : e ∈ Submonoid.closure S := by
    have htop := Equiv.Perm.mclosure_swap_castSucc_succ (n + 1)
    change e ∈ Submonoid.closure
      (Set.range (fun j : Fin (n + 1) ↦ Equiv.swap j.castSucc j.succ))
    rw [htop]
    exact Set.mem_univ e
  have hgood : ExactPermutationProperty K d n e := by
    refine Submonoid.closure_induction (motive := fun q _ ↦
      ExactPermutationProperty K d n q) ?_ ?_ ?_ he
    · intro q hq
      rcases hq with ⟨j, rfl⟩
      exact fun U ↦
        mme_kronFin_adjacent_swap_equiv_preserves_tensor_and_basis U j
    · exact exactPermutationProperty_one
    · intro a b _ _ ha hb
      exact exactPermutationProperty_mul a b ha hb
  exact hgood T

end MME.TensorObj

theorem solution :
    ∀ {K : Type u} [Field K] {d n : ℕ}
      (T : Fin (n + 2) → TensorObj K d)
      (e : Equiv.Perm (Fin (n + 2))),
    ∃ F : ∀ i : Fin d,
        (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).V i ≃ₗ[K]
          (TensorObj.kronFin (n + 2) T).V i,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (TensorObj.kronFin (n + 2) (fun r ↦ T (e r))).t =
        (TensorObj.kronFin (n + 2) T).t ∧
      ∀ (i : Fin d) (index : Fin (n + 2) → Type u)
        (b : ∀ r, Basis (index r) K ((T r).V i))
        (w : ∀ r, index (e r)),
        F i
            (TensorObj.kronFinModePiBasis (n + 2)
              (fun r ↦ T (e r)) i (fun r ↦ b (e r)) w) =
          TensorObj.kronFinModePiBasis (n + 2) T i b
            (Equiv.piCongrLeft index e w) :=
  MME.TensorObj.mme_kronFin_perm_preserves_tensor_and_basis
