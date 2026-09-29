-- Prove2me | solution 1 for mme_dwz_generic_basis_label_hole_cover_tensor_repair
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-16T15:22:51.379668+00:00
-- url     : https://prove2.me/submissions/92319742-cd58-4ab0-879d-016562b7dcee

import Theorems.Thm_mme_dwz_basis_label_owner_map_singleton
import Theorems.Thm_mme_dwz_hole_cover_exact_once_tensor_repair_poly
import Mathlib.Tactic

open MME Module PiTensorProduct
open MME.DWZComponentRestriction MME.DWZSquare
open scoped BigOperators
universe u v w z
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

namespace DWZGenericHoleRepair

variable {K : Type u} [Field K] (X : TensorObj K 3)

noncomputable def zModes (P : X.V 2 →ₗ[K] X.V 2) :
    ∀ i, X.V i →ₗ[K] X.V i :=
  Function.update (fun _ ↦ LinearMap.id) 2 P

noncomputable def zTensorLinear :
    (X.V 2 →ₗ[K] X.V 2) →ₗ[K]
      (PiTensorProduct K X.V →ₗ[K] PiTensorProduct K X.V) :=
  (PiTensorProduct.mapMultilinear K X.V X.V).toLinearMap
    (fun _ ↦ LinearMap.id) 2

theorem zTensorLinear_apply (P : X.V 2 →ₗ[K] X.V 2) :
    zTensorLinear X P = PiTensorProduct.map (zModes X P) := rfl

variable {ι : Type z} {Block : Type w}
  [Fintype Block] [DecidableEq Block]
  (b : Basis ι K (X.V 2)) (label : ι → Block)

omit [Fintype Block] in
theorem projection_sum (blocks : Finset Block) :
    basisLabelProjection b label blocks =
      ∑ block ∈ blocks, basisLabelProjection b label {block} := by
  classical
  apply b.ext
  intro i
  simp [basisLabelProjection, Finset.sum_apply]

theorem projection_univ :
    basisLabelProjection b label Finset.univ = LinearMap.id := by
  apply b.ext
  intro i
  simp [basisLabelProjection]

theorem tensor_projection_sum (blocks : Finset Block) :
    PiTensorProduct.map (zModes X (basisLabelProjection b label blocks)) X.t =
      ∑ block : Block, if block ∈ blocks then
        PiTensorProduct.map (zModes X (basisLabelProjection b label {block})) X.t
      else 0 := by
  classical
  have h := congrArg (fun P ↦ (zTensorLinear X P) X.t)
    (projection_sum X b label blocks)
  simpa [map_sum, LinearMap.sum_apply, zTensorLinear_apply,
    ← Finset.sum_filter] using h

theorem tensor_projection_univ :
    (∑ block : Block,
      PiTensorProduct.map (zModes X (basisLabelProjection b label {block})) X.t) =
      X.t := by
  have h := tensor_projection_sum X b label Finset.univ
  rw [projection_univ X b label] at h
  simpa [zModes, PiTensorProduct.map_id] using h.symm

omit [Fintype Block] in
theorem shuffle_projection
    (g : Equiv.Perm Block) (perm : Equiv.Perm ι)
    (f : ∀ i, X.V i →ₗ[K] X.V i)
    (hZ : ∀ i, f 2 (b i) = b (perm i))
    (hlabel : ∀ i, label (perm i) = g (label i))
    (blocks : Finset Block) :
    PiTensorProduct.map f
        (PiTensorProduct.map (zModes X (basisLabelProjection b label blocks)) X.t) =
      PiTensorProduct.map
        (zModes X (basisLabelProjection b label (blocks.image g)))
        (PiTensorProduct.map f X.t) := by
  classical
  have hz : (f 2).comp (basisLabelProjection b label blocks) =
      (basisLabelProjection b label (blocks.image g)).comp (f 2) := by
    apply b.ext
    intro i
    simp only [LinearMap.comp_apply, basisLabelProjection, Basis.constr_basis, hZ]
    rw [hlabel]
    simp only [Finset.mem_image, g.injective.eq_iff, exists_eq_right]
    by_cases hi : label i ∈ blocks <;> simp [hi, hZ]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp,
    ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  congr 2
  funext i
  fin_cases i
  · rfl
  · rfl
  · exact hz

theorem shuffled_broken_tensor
    (g : Equiv.Perm Block) (perm : Equiv.Perm ι)
    (f : ∀ i, X.V i →ₗ[K] X.V i)
    (hZ : ∀ i, f 2 (b i) = b (perm i))
    (hlabel : ∀ i, label (perm i) = g (label i))
    (hX : PiTensorProduct.map f X.t = X.t)
    (blocks : Finset Block) :
    PiTensorProduct.map f
        (PiTensorProduct.map (zModes X (basisLabelProjection b label blocks)) X.t) =
      ∑ block : Block, if g.symm block ∈ blocks then
        PiTensorProduct.map (zModes X (basisLabelProjection b label {block})) X.t
      else 0 := by
  rw [shuffle_projection X b label g perm f hZ hlabel blocks, hX,
    tensor_projection_sum X b label]
  apply Finset.sum_congr rfl
  intro block _
  have hmem : block ∈ blocks.image g ↔ g.symm block ∈ blocks := by
    constructor
    · intro h
      obtain ⟨a, ha, hab⟩ := Finset.mem_image.mp h
      simpa [← hab] using ha
    · intro h
      exact Finset.mem_image.mpr ⟨g.symm block, h, g.apply_symm_apply block⟩
  simp only [hmem]

theorem owner_realizes
    {s : ℕ} (owner : Block → Fin s) (t : Fin s)
    (g : Equiv.Perm Block) (perm : Equiv.Perm ι)
    (f : ∀ i, X.V i →ₗ[K] X.V i)
    (hZ : ∀ i, f 2 (b i) = b (perm i))
    (hlabel : ∀ i, label (perm i) = g (label i))
    (hX : PiTensorProduct.map f X.t = X.t)
    (blocks : Finset Block)
    (hcovered : ∀ block, t = owner block → g.symm block ∈ blocks) :
    PiTensorProduct.map
        (fun i ↦ (zModes X (basisLabelProjection b label
          (Finset.univ.filter (fun block ↦ t = owner block))) i).comp (f i))
        (PiTensorProduct.map (zModes X (basisLabelProjection b label blocks)) X.t) =
      ∑ block : Block, if t = owner block then
        PiTensorProduct.map (zModes X (basisLabelProjection b label {block})) X.t
      else 0 := by
  classical
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply,
    shuffled_broken_tensor X b label g perm f hZ hlabel hX blocks, map_sum]
  apply Finset.sum_congr rfl
  intro block _
  have howner := mme_dwz_basis_label_owner_map_singleton X b label owner t block
  by_cases ho : t = owner block
  · rw [if_pos (hcovered block ho)]
    exact howner
  · by_cases hn : g.symm block ∈ blocks
    · rw [if_pos hn]
      exact howner
    · simp [hn, ho]

end DWZGenericHoleRepair

theorem solution
    {K : Type u} [Field K] (X : TensorObj K 3)
    {ι : Type z} {Block : Type w} {Shuffle : Type v}
    [Fintype Block] [DecidableEq Block] [Nonempty Block]
    [Fintype Shuffle] [DecidableEq Shuffle] [Nonempty Shuffle]
    (b : Basis ι K (X.V 2)) (label : ι → Block)
    (system : AvailableBlockShuffle Block Shuffle)
    (shuffleMap : Shuffle → ∀ i, X.V i →ₗ[K] X.V i)
    (basisPerm : Shuffle → Equiv.Perm ι)
    (hZ : ∀ g i, shuffleMap g 2 (b i) = b (basisPerm g i))
    (hlabel : ∀ g i, label (basisPerm g i) = system.move g (label i))
    (hX : ∀ g, PiTensorProduct.map (shuffleMap g) X.t = X.t)
    (N ell s : ℕ) (hN : 0 < N) (hell : 0 < ell)
    (copies : Fin s → BrokenBlockCopy Block)
    (hcard : Fintype.card Block ≤ 2 ^ (N * ell))
    (hsum : ((N * ell + 1 : ℕ) : ℝ) ≤
      ∑ t : Fin s, nonholeFraction (copies t)) :
    let source : Fin s → TensorObj K 3 := fun t ↦
      { V := X.V
        t := PiTensorProduct.map
          (Function.update (fun _ ↦ LinearMap.id) 2
            (basisLabelProjection b label (copies t).nonholes)) X.t }
    ∃ (shuffles : Fin s → Shuffle) (owner : Block → Fin s)
        (f : ∀ t i, (source t).V i →ₗ[K] X.V i),
      (∀ block : Block,
        (system.move (shuffles (owner block))).symm block ∈
          (copies (owner block)).nonholes) ∧
      (∀ t, f t 0 = shuffleMap (shuffles t) 0) ∧
      (∀ t, f t 1 = shuffleMap (shuffles t) 1) ∧
      (∀ t, PiTensorProduct.map (f t) (source t).t =
        ∑ block : Block, if t = owner block then
          PiTensorProduct.map
            (Function.update (fun _ ↦ LinearMap.id) 2
              (basisLabelProjection b label {block})) X.t
        else 0) ∧
      TensorObj.Restrict X (TensorObj.bigAdd source) := by
  classical
  dsimp only
  let source : Fin s → TensorObj K 3 := fun t ↦
    { V := X.V
      t := PiTensorProduct.map
        (Function.update (fun _ ↦ LinearMap.id) 2
          (basisLabelProjection b label (copies t).nonholes)) X.t }
  let blockTensor := fun block : Block ↦
    PiTensorProduct.map
      (Function.update (fun _ ↦ LinearMap.id) 2
        (basisLabelProjection b label {block})) X.t
  have hrepair := mme_dwz_hole_cover_exact_once_tensor_repair_poly
    system N ell hN hell copies hcard hsum source blockTensor
    (fun shuffles t ↦ shuffleMap (shuffles t)) ?_
  · obtain ⟨shuffles, owner, f, _, hcover, hf0, hf1, howned, hrestrict⟩ := hrepair
    refine ⟨shuffles, owner, f, hcover, hf0, hf1, howned, ?_⟩
    have hsumBlocks : (∑ block : Block, blockTensor block) = X.t :=
      DWZGenericHoleRepair.tensor_projection_univ X b label
    simpa only [hsumBlocks] using hrestrict
  · intro shuffles owner hcovered
    let f : ∀ t i, (source t).V i →ₗ[K] X.V i := fun t i ↦
      (DWZGenericHoleRepair.zModes X (basisLabelProjection b label
        (Finset.univ.filter (fun block ↦ t = owner block))) i).comp
        (shuffleMap (shuffles t) i)
    refine ⟨f, ?_, ?_, ?_⟩
    · intro t
      simp [f, DWZGenericHoleRepair.zModes]
    · intro t
      simp [f, DWZGenericHoleRepair.zModes]
    · intro t
      exact DWZGenericHoleRepair.owner_realizes X b label owner t
        (system.move (shuffles t)) (basisPerm (shuffles t))
        (shuffleMap (shuffles t)) (hZ (shuffles t)) (hlabel (shuffles t))
        (hX (shuffles t)) (copies t).nonholes
        (fun block h ↦ by simpa [h] using hcovered block)
