-- Prove2me | solution 1 for mme_complete_split_restrictedPower_chunk_symmetry
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:26:18.115155+00:00
-- url     : https://prove2.me/submissions/fa03e3ad-eb98-4d39-9997-47e18e295b5c

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Definitions.Def_mme_TypeGrading_kron
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.Data.Finset.Card

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  PiTensorProduct Module
open scoped NNReal

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

private theorem count_reindex {I : Type u} {ell N : ℕ}
    (label : I → CompleteWord ell) (w : PowIndex I N)
    (e : Equiv.Perm (Fin N)) (sigma : CompleteWord ell) :
    wordCount label (PowIndex.reindex e w) sigma = wordCount label w sigma := by
  classical
  unfold wordCount
  exact Finset.card_equiv e (by intro r; simp [PowIndex.get_reindex])

private theorem consistent_reindex {I : Type u} {ell N : ℕ}
    (label : I → CompleteWord ell) (beta : Profile ell)
    (epsilon : ℝ≥0) (w : PowIndex I N) (e : Equiv.Perm (Fin N)) :
    ApproxConsistent label beta epsilon (PowIndex.reindex e w) ↔
      ApproxConsistent label beta epsilon w := by
  simp only [ApproxConsistent, count_reindex]

private def indexReindexEquiv (I : Type u) (N : ℕ)
    (e : Equiv.Perm (Fin N)) : PowIndex I N ≃ PowIndex I N where
  toFun := PowIndex.reindex e
  invFun := PowIndex.reindex e.symm
  left_inv := PowIndex.reindex_symm_reindex e
  right_inv w := by
    simpa only [Equiv.symm_symm] using PowIndex.reindex_symm_reindex e.symm w

private theorem allowed_class_span
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : ∀ i, I i → Prop) (i : Fin 3) :
    (T.basisAllAllowedGrading b allowed).classOf i 0 =
      Submodule.span K (b i '' {w | allowed i w}) := by
  classical
  change Submodule.span K
    (b i '' {w | (if allowed i w then (0 : Fin 2) else 1) = 0}) = _
  have hs : {w | (if allowed i w then (0 : Fin 2) else 1) = 0} =
      {w | allowed i w} := by
    ext w
    simp
  rw [hs]

private theorem allowed_automorphism
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : ∀ i, I i → Prop)
    (P : ∀ i, T.V i ≃ₗ[K] T.V i)
    (idx : ∀ i, I i ≃ I i)
    (hb : ∀ i w, P i (b i w) = b i (idx i w))
    (ha : ∀ i w, allowed i (idx i w) ↔ allowed i w)
    (ht : PiTensorProduct.map (fun i ↦ (P i).toLinearMap) T.t = T.t) :
    let G := T.basisAllAllowedGrading b allowed
    ∃ Ψ : ∀ i, (G.blockSubtensor (fun _ ↦ 0)).V i ≃ₗ[K]
        (G.blockSubtensor (fun _ ↦ 0)).V i,
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t =
        (G.blockSubtensor (fun _ ↦ 0)).t ∧
      ∀ i, (G.classOf i 0).subtype.comp (Ψ i).toLinearMap =
        (P i).toLinearMap.comp (G.classOf i 0).subtype := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hmap (i : Fin 3) :
      Submodule.map (P i).toLinearMap (G.classOf i 0) = G.classOf i 0 := by
    rw [allowed_class_span, Submodule.map_span]
    congr 1
    ext x
    constructor
    · rintro ⟨y, ⟨w, hw, rfl⟩, rfl⟩
      exact ⟨idx i w, (ha i w).2 hw, (hb i w).symm⟩
    · rintro ⟨w, hw, rfl⟩
      refine ⟨b i ((idx i).symm w), ⟨(idx i).symm w, ?_, rfl⟩, ?_⟩
      · exact (ha i ((idx i).symm w)).1 (by simpa using hw)
      · simpa using hb i ((idx i).symm w)
  let Ψ : ∀ i, (G.blockSubtensor (fun _ ↦ 0)).V i ≃ₗ[K]
      (G.blockSubtensor (fun _ ↦ 0)).V i :=
    fun i ↦ (P i).ofSubmodules (G.classOf i 0) (G.classOf i 0) (hmap i)
  have hcomm (i : Fin 3) :
      (Ψ i).toLinearMap.comp (G.blockProj i 0) =
        (G.blockProj i 0).comp (P i).toLinearMap := by
    apply (b i).ext
    intro w
    change Ψ i (G.blockProj i 0 (b i w)) = G.blockProj i 0 (P i (b i w))
    by_cases hw : allowed i w
    · have hmem : b i w ∈ G.classOf i 0 := by
        rw [allowed_class_span]
        exact Submodule.subset_span ⟨w, hw, rfl⟩
      have hmem' : b i (idx i w) ∈ G.classOf i 0 := by
        rw [allowed_class_span]
        exact Submodule.subset_span ⟨idx i w, (ha i w).2 hw, rfl⟩
      rw [hb i w, TensorObj.TypeGrading.blockProj_apply_mem G i 0 (b i w) hmem,
        TensorObj.TypeGrading.blockProj_apply_mem G i 0 (b i (idx i w)) hmem']
      apply Subtype.ext
      exact hb i w
    · have hmem : b i w ∈ G.classOf i 1 := by
        change b i w ∈ Submodule.span K
          (b i '' {w | (if allowed i w then (0 : Fin 2) else 1) = 1})
        exact Submodule.subset_span ⟨w, by simp [hw], rfl⟩
      have hnot : ¬ allowed i (idx i w) := fun h ↦ hw ((ha i w).1 h)
      have hmem' : b i (idx i w) ∈ G.classOf i 1 := by
        change b i (idx i w) ∈ Submodule.span K
          (b i '' {w | (if allowed i w then (0 : Fin 2) else 1) = 1})
        exact Submodule.subset_span ⟨idx i w, by simp [hnot], rfl⟩
      rw [TensorObj.TypeGrading.blockProj_apply_mem_ne G i 0 1 (by decide)
          (b i w) hmem, hb i w,
        TensorObj.TypeGrading.blockProj_apply_mem_ne G i 0 1 (by decide)
          (b i (idx i w)) hmem']
      exact (Ψ i).map_zero
  refine ⟨Ψ, ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) =
        PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t
    calc
      _ = PiTensorProduct.map
          (fun i ↦ (Ψ i).toLinearMap.comp (G.blockProj i 0)) T.t :=
        (LinearMap.congr_fun (PiTensorProduct.map_comp
          (f := fun i ↦ G.blockProj i 0)
          (g := fun i ↦ (Ψ i).toLinearMap)) T.t).symm
      _ = PiTensorProduct.map
          (fun i ↦ (G.blockProj i 0).comp (P i).toLinearMap) T.t := by
        exact congrArg (fun f ↦ PiTensorProduct.map f T.t) (funext hcomm)
      _ = PiTensorProduct.map (fun i ↦ G.blockProj i 0)
          (PiTensorProduct.map (fun i ↦ (P i).toLinearMap) T.t) :=
        LinearMap.congr_fun (PiTensorProduct.map_comp
          (f := fun i ↦ (P i).toLinearMap)
          (g := fun i ↦ G.blockProj i 0)) T.t
      _ = _ := by rw [ht]
  · intro i
    ext x
    rfl

/-- One common chunk shuffle preserves exact histograms and the actual
all-mode restricted tensor, including its literal ambient inclusions.
This is invariance, not transitivity of an approximate-profile union. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (epsilon : ℝ≥0)
    (N : ℕ) (e : Equiv.Perm (Fin N)) :
    let G := (T.kronPow N).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) epsilon)
    (∀ (i : Fin 3) (w : PowIndex (I i) N) (sigma : CompleteWord ell),
      wordCount (label i) (PowIndex.reindex e w) sigma = wordCount (label i) w sigma) ∧
    ∃ Ψ : ∀ i, (restrictedPower T b label beta epsilon N).V i ≃ₗ[K]
        (restrictedPower T b label beta epsilon N).V i,
      PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap)
          (restrictedPower T b label beta epsilon N).t =
        (restrictedPower T b label beta epsilon N).t ∧
      ∀ i, (G.classOf i 0).subtype.comp (Ψ i).toLinearMap =
        (kronPowModePositionEquiv T i (b i) N e).toLinearMap.comp
          (G.classOf i 0).subtype := by
  refine ⟨fun i w sigma ↦ count_reindex (label i) w e sigma, ?_⟩
  let P := fun i ↦ kronPowModePositionEquiv T i (b i) N e
  obtain ⟨P', hb', ht'⟩ := mme_kronPow_position_permutation_linear_equiv T b N e
  have hPP' : P' = P := by
    funext i
    apply LinearEquiv.toLinearMap_injective
    apply (kronPowModeWordBasis T i (b i) N).ext
    intro w
    change P' i (kronPowModeWordBasis T i (b i) N w) = _
    rw [hb']
    exact (Basis.equiv_apply
      (b := kronPowModeWordBasis T i (b i) N) (i := w)
      (b' := kronPowModeWordBasis T i (b i) N)
      (e := kronPowWordReindex e (I i))).symm
  have ht : PiTensorProduct.map (fun i ↦ (P i).toLinearMap)
      (T.kronPow N).t = (T.kronPow N).t := by
    rw [← hPP']
    exact ht'
  exact allowed_automorphism (T.kronPow N)
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (label i) (beta i) epsilon) P
    (fun i ↦ indexReindexEquiv (I i) N e)
    (fun i w ↦ mme_kronPow_position_permutation_recursive_basis T i (b i) N e w)
    (fun i w ↦ consistent_reindex (label i) (beta i) epsilon w e) ht
