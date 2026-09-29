-- Prove2me | solution 1 for mme_gradedAddressProj_preserves_kronPow_tensor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T14:25:13.023644+00:00
-- url     : https://prove2.me/submissions/4c1f5113-82c5-4577-8354-87472851f0d2

import Definitions.Def_mme_induced_word_zeroing

open MME PiTensorProduct

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem gradedAddressProj_interchange_tprod
    {K : Type u} [Field K]
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem gradedAddressProj_map_interchange
    {K : Type u} [Field K]
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [gradedAddressProj_interchange_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod,
            gradedAddressProj_interchange_tprod]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

theorem solution
    {K : Type u} [Field K]
    {T : TensorObj K 3} {t R : ℕ}
    (G : T.TypeGrading t) (address : Fin 3 → Fin R → Fin t) :
    PiTensorProduct.map (gradedAddressProj G R address)
        (T.kronPow R).t =
      (gradedAddressBlock G address).t := by
  induction R with
  | zero =>
      change PiTensorProduct.map (fun _ ↦ LinearMap.id)
          (TensorObj.oneObj : TensorObj K 3).t =
        (TensorObj.oneObj : TensorObj K 3).t
      rw [PiTensorProduct.map_id]
      rfl
  | succ R ih =>
      change PiTensorProduct.map
          (fun i ↦ TensorProduct.map
            (G.blockProj i (address i 0))
            (gradedAddressProj G R
              (fun i' j ↦ address i' j.succ) i))
          (interchange T.t (T.kronPow R).t) =
        interchange
          (G.blockTensor (fun i ↦ address i 0))
          (gradedAddressBlock G
            (fun i j ↦ address i j.succ)).t
      rw [gradedAddressProj_map_interchange]
      unfold TensorObj.TypeGrading.blockTensor
      rw [ih]
