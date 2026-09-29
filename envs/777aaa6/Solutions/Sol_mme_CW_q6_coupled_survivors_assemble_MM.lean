-- Prove2me | solution 1 for mme_CW_q6_coupled_survivors_assemble_MM
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T05:34:12.237762+00:00
-- url     : https://prove2.me/submissions/41620d1a-c2b8-40b6-ab09-d4a7944c5804

import Definitions.Def_mme_CW_q6_coupled_survivor
import Definitions.Def_mme_mmobj_mul
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_CW_coupled_cyclic_high_MM_restrict
import Theorems.Thm_mme_CW_coupled_cyclic_low_MM_restrict
import Theorems.Thm_mme_restrict_kronPow
import Theorems.Thm_mme_MMObj_square_kronPow_iso
import Theorems.Thm_mme_bigAdd_mono_restrict

open MME PiTensorProduct TensorProduct

universe u

namespace CWQ6CoupledSurvivorsAssembleMM

theorem interchange_tprod
    {K : Type u} [Field K]
    {I : Type*} [Fintype I] [DecidableEq I]
    {V W : I → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    MME.interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (MME.interchange (tprod K v)) (tprod K w) = _
  unfold MME.interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (MME.interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem map_interchange
    {K : Type u} [Field K]
    {I : Type*} [Fintype I] [DecidableEq I]
    {V₁ V₂ V₃ V₄ : I → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (MME.interchange t₁ t₂) =
      MME.interchange (PiTensorProduct.map f t₁)
        (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction t₂ using PiTensorProduct.induction_on with
    | smul_tprod c' v' =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        interchange_tprod]
      simp only [TensorProduct.map_tmul]
    | add x y ihx ihy => simp only [map_add, ihx, ihy]
  | add x y ihx ihy => simp only [map_add, LinearMap.add_apply, ihx, ihy]

theorem kron_restrict
    {K : Type u} [Field K] {d : ℕ}
    {X X' Y Y' : TensorObj K d}
    (hX : TensorObj.Restrict X X') (hY : TensorObj.Restrict Y Y') :
    TensorObj.Restrict (TensorObj.kron X Y)
      (TensorObj.kron X' Y') := by
  obtain ⟨f, hf⟩ := hX
  obtain ⟨g, hg⟩ := hY
  refine ⟨fun i => TensorProduct.map (f i) (g i), ?_⟩
  show PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
      (MME.interchange X'.t Y'.t) = MME.interchange X.t Y.t
  rw [map_interchange, hf, hg]

theorem one_survivor
    {K : Type u} [Field K] (L G : ℕ) :
    TensorObj.Restrict
      (MMObj K
        (36 ^ (2 * G) * 6 ^ (2 * L))
        (36 ^ (2 * G) * 6 ^ (2 * L))
        (36 ^ (2 * G) * 6 ^ (2 * L)))
      (coupledQ6Survivor K L G) := by
  have hhighBase : TensorObj.Restrict
      (MMObj K 36 36 36)
      (cyclicSymmetrization (MMObj K 6 1 6)) := by
    simpa using mme_CW_coupled_cyclic_high_MM_restrict (K := K) 6
  have hlowBase : TensorObj.Restrict
      (MMObj K 6 6 6)
      (cyclicSymmetrization (MMObj K 1 6 1)) := by
    simpa using mme_CW_coupled_cyclic_low_MM_restrict (K := K) 6
  have hhighPow := mme_restrict_kronPow hhighBase (2 * G)
  have hlowPow := mme_restrict_kronPow hlowBase (2 * L)
  have hhigh : TensorObj.Restrict
      (MMObj K (36 ^ (2 * G)) (36 ^ (2 * G)) (36 ^ (2 * G)))
      ((cyclicSymmetrization (MMObj K 6 1 6)).kronPow (2 * G)) :=
    TensorObj.Restrict.trans
      (mme_MMObj_square_kronPow_iso (K := K) 36 (2 * G)).2 hhighPow
  have hlow : TensorObj.Restrict
      (MMObj K (6 ^ (2 * L)) (6 ^ (2 * L)) (6 ^ (2 * L)))
      ((cyclicSymmetrization (MMObj K 1 6 1)).kronPow (2 * L)) :=
    TensorObj.Restrict.trans
      (mme_MMObj_square_kronPow_iso (K := K) 6 (2 * L)).2 hlowPow
  have hproduct := kron_restrict hhigh hlow
  exact TensorObj.Restrict.trans
    (MMObj_kron_iso (K := K)
      (36 ^ (2 * G)) (36 ^ (2 * G)) (36 ^ (2 * G))
      (6 ^ (2 * L)) (6 ^ (2 * L)) (6 ^ (2 * L))).2
    hproduct

end CWQ6CoupledSurvivorsAssembleMM

theorem solution
    {K : Type u} [Field K] (L G k : ℕ) :
    TensorObj.Restrict
      (TensorObj.bigAdd (fun _ : Fin k =>
        MMObj K
          (36 ^ (2 * G) * 6 ^ (2 * L))
          (36 ^ (2 * G) * 6 ^ (2 * L))
          (36 ^ (2 * G) * 6 ^ (2 * L))))
      (TensorObj.bigAdd (fun _ : Fin k => coupledQ6Survivor K L G)) := by
  apply mme_bigAdd_mono_restrict
  intro j
  exact CWQ6CoupledSurvivorsAssembleMM.one_survivor L G
