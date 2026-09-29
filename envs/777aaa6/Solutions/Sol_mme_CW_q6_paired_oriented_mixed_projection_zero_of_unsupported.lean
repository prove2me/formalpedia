-- Prove2me | solution 1 for mme_CW_q6_paired_oriented_mixed_projection_zero_of_unsupported
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T00:17:24.117853+00:00
-- url     : https://prove2.me/submissions/4828d8fe-e3b6-4dcd-bcaf-f47c47ffb26a

import Mathlib.LinearAlgebra.PiTensorProduct
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_CW_q6_common_halving_paired_oriented_component_data
import Definitions.Def_mme_CW_q6_paired_cyclic_induced
import Theorems.Thm_mme_dwz_q6_explicit_coupled_four_block_support

/-!
Mixed projections of the paired oriented coupled tensor vanish outside paired
cyclic support. The word-projection induction below adapts the accepted proof
of `mme_induced_graded_address_blocks_restrict` to arbitrary entry indices.
The coupled coordinate-support theorem is imported with its actual proof in
the local audit environment. No paired-inducedness assumption is used here.
-/

open MME PiTensorProduct BigOperators

set_option autoImplicit false

universe u

namespace MME

namespace InducedWordZeroing

variable {K : Type u} [Field K]

local notation "addressProj" => MME.gradedAddressProj
local notation "bigAddSlot" => MME.gradedBigAddSlot

/-- Naturality of the mode-wise interchange map. -/
private theorem interchange_tprod
    {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i => v i ⊗ₜ[K] w i) := by
  show (interchange (tprod K v)) (tprod K w) = _
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  show (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

theorem map_interchange
    {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (t₁ : PiTensorProduct K V₁) (t₂ : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i => TensorProduct.map (f i) (g i))
        (interchange t₁ t₂) =
      interchange (PiTensorProduct.map f t₁) (PiTensorProduct.map g t₂) := by
  induction t₁ using PiTensorProduct.induction_on with
  | smul_tprod c v =>
      induction t₂ using PiTensorProduct.induction_on with
      | smul_tprod c' v' =>
          simp only [map_smul, LinearMap.smul_apply]
          rw [interchange_tprod, PiTensorProduct.map_tprod,
            PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
            interchange_tprod]
          simp only [TensorProduct.map_tmul]
      | add x y ih₁ ih₂ =>
          simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ =>
      simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

/-- A mixed choice of one retained address per tensor mode projects to zero
as soon as one coordinate grading block is zero. -/
theorem mixed_projection_eq_zero_of_coord
    {T : TensorObj K 3} {t N : ℕ} {ι : Type*}
    (G : T.TypeGrading t)
    (A : ι → Fin 3 → Fin N → Fin t)
    (js : Fin 3 → ι) (r : Fin N)
    (hr : G.blockTensor (fun i => A (js i) i r) = 0) :
    PiTensorProduct.map
        (fun i => addressProj G N (A (js i)) i)
        (T.kronPow N).t = 0 := by
  induction N with
  | zero => exact Fin.elim0 r
  | succ N ih =>
      refine Fin.cases
        (motive := fun r =>
          G.blockTensor (fun i => A (js i) i r) = 0 →
          PiTensorProduct.map
              (fun i => addressProj G (N + 1) (A (js i)) i)
              (T.kronPow (N + 1)).t = 0)
        ?_ (fun r' => ?_) r hr
      · intro hr0
        simp only [MME.gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (G.blockProj i (A (js i) i 0))
              (addressProj G N
                (fun i' r => A (js i) i' r.succ) i))
            (interchange T.t (T.kronPow N).t) = 0
        rw [map_interchange]
        have hfirst :
            PiTensorProduct.map
                (fun i => G.blockProj i (A (js i) i 0)) T.t =
              G.blockTensor (fun i => A (js i) i 0) := rfl
        rw [hfirst, hr0]
        simp only [map_zero, LinearMap.zero_apply]
      · intro hr'
        simp only [MME.gradedAddressProj, TensorObj.kronPow]
        change PiTensorProduct.map
            (fun i => TensorProduct.map
              (G.blockProj i (A (js i) i 0))
              (addressProj G N
                (fun i' r => A (js i) i' r.succ) i))
            (interchange T.t (T.kronPow N).t) = 0
        rw [map_interchange]
        have htail := ih (fun j i r => A j i r.succ) r' hr'
        rw [htail]
        exact LinearMap.map_zero _


end InducedWordZeroing
end MME

namespace MME.PairedOrientedPackaging

open MME.DWZComponentRestriction MME.InducedWordZeroing

variable {K : Type u} [Field K] {N L G A H : ℕ}

private theorem coupled_block_zero_of_not_supported
    (σ : Fin 3 → Fin 3)
    (h : ¬ CWQ6CoupledLocalSupported (σ 0) (σ 1) (σ 2)) :
    (dwzQ6CoupledGrading K).blockTensor σ = 0 := by
  apply mme_dwz_q6_explicit_coupled_four_block_support
  all_goals
    intro heq
    subst σ
    exact h (by simp [CWQ6CoupledLocalSupported])

private theorem permuted_block_zero_of_not_supported
    (e : Equiv.Perm (Fin 3)) (σ : Fin 3 → Fin 3)
    (h : ¬ CWQ6CoupledLocalSupported (σ (e 0)) (σ (e 1)) (σ (e 2))) :
    (TensorObj.TypeGrading.permObjGrading
      (dwzQ6CoupledGrading K) e).blockTensor σ = 0 := by
  let ρ : Fin 3 → Fin 3 := fun i => σ (e i)
  have hσ : σ = fun i => ρ (e.symm i) := by
    funext i
    simp [ρ]
  have hz := coupled_block_zero_of_not_supported (K := K) ρ h
  rw [hσ, TensorObj.TypeGrading.permObjGrading_blockTensor, hz, map_zero]
  rfl

/-- An unsupported mixed triple of half-addresses annihilates the literal
paired tensor projection, before any direct-sum packaging is chosen. -/
theorem mixed_component_projection_eq_zero
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H)
    (h : ¬ family.PairedCyclicSupported halving (js 0) (js 1) (js 2)) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t = 0 := by
  classical
  change PiTensorProduct.map
    (fun i => TensorProduct.map
      (gradedAddressProj (leftGrading (K := K)) N
        (leftAddress family halving (js i)) i)
      (gradedAddressProj (rightGrading (K := K)) N
        (rightAddress family halving (js i)) i))
    (interchange _ _) = 0
  rw [map_interchange]
  rw [CWQ6PrimaryHashFamily.PairedCyclicSupported] at h
  rcases not_and_or.mp h with hleft | hright
  · obtain ⟨r, hr⟩ := not_forall.mp hleft
    have hz :
        (leftGrading (K := K)).blockTensor
          (fun i => leftAddress family halving (js i) i r) = 0 := by
      apply permuted_block_zero_of_not_supported
      simpa [leftAddress, cyclicPerm] using hr
    rw [mixed_projection_eq_zero_of_coord
      (leftGrading (K := K)) (leftAddress family halving) js r hz]
    simp only [map_zero, LinearMap.zero_apply]
  · obtain ⟨r, hr⟩ := not_forall.mp hright
    have hz :
        (rightGrading (K := K)).blockTensor
          (fun i => rightAddress family halving (js i) i r) = 0 := by
      apply permuted_block_zero_of_not_supported
      simpa [rightAddress, cyclicPerm] using hr
    rw [mixed_projection_eq_zero_of_coord
      (rightGrading (K := K)) (rightAddress family halving) js r hz]
    exact LinearMap.map_zero _

end MME.PairedOrientedPackaging

open MME MME.PairedOrientedPackaging

theorem solution
    {K : Type u} [Field K] {N L G A H : ℕ}
    (family : CWQ6PrimaryHashFamily N L G A H)
    (halving : family.CommonBalancedXYHalving)
    (js : Fin 3 → Fin A × Fin H)
    (h : ¬ family.PairedCyclicSupported halving (js 0) (js 1) (js 2)) :
    PiTensorProduct.map (fun i => componentProj (K := K) family halving (js i) i)
      (TensorObj.kron
        ((TensorObj.permObj (cyclicPerm.trans cyclicPerm)
          (coupledObj K 6)).kronPow N)
        ((TensorObj.permObj cyclicPerm (coupledObj K 6)).kronPow N)).t = 0 := by
  exact mixed_component_projection_eq_zero family halving js h
