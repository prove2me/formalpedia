-- Prove2me | solution 1 for mme_complete_split_exact_restrictedPower_uniform_basis_interface
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T04:50:07.121717+00:00
-- url     : https://prove2.me/submissions/8ac520a3-18d2-4755-88d9-6a1a8eff13f0

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_dwz_hole_cover_data
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Theorems.Thm_mme_complete_split_restrictedPower_chunk_symmetry
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Theorems.Thm_mme_complete_split_exact_type_uniform_chunk_shuffle
import Mathlib.LinearAlgebra.Basis.Submodule
import Mathlib.Data.Fintype.Perm

open MME MME.TensorObj MME.CompleteSplit MME.DWZComponentRestriction
  MME.DWZSquare PiTensorProduct Module
open scoped Classical NNReal

universe u

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

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

private theorem allowed_basis_exists
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : ∀ i, I i → Prop) (i : Fin 3) :
    ∃ B : Basis {w : I i // allowed i w} K
        ((T.basisAllAllowedSubtensor b allowed).V i),
      ∀ w, ((T.basisAllAllowedGrading b allowed).classOf i 0).subtype (B w) =
        b i w.1 := by
  let v : {w : I i // allowed i w} → T.V i := fun w ↦ b i w.1
  have hv : LinearIndependent K v :=
    (b i).linearIndependent.comp (fun w : {w : I i // allowed i w} ↦ w.1)
      Subtype.val_injective
  have hrange : Set.range v = b i '' {w | allowed i w} := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact ⟨w.1, w.2, rfl⟩
    · rintro ⟨w, hw, rfl⟩
      exact ⟨⟨w, hw⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) =
      (T.basisAllAllowedGrading b allowed).classOf i 0 := by
    rw [hrange, allowed_class_span]
  let B : Basis {w : I i // allowed i w} K
      ((T.basisAllAllowedSubtensor b allowed).V i) :=
    (Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)
  refine ⟨B, ?_⟩
  intro w
  change ↑(((Basis.span hv).map (LinearEquiv.ofEq _ _ hspan)) w) = b i w.1
  rw [Module.Basis.map_apply]
  change ↑((Basis.span hv) w) = b i w.1
  rw [Module.Basis.span_apply]

private def labelWord {I : Type u} {ell N : ℕ}
    (label : I → CompleteWord ell) (w : PowIndex I N) :
    PowIndex (CompleteWord ell) N :=
  PowIndex.ofFun N (fun r ↦ label (PowIndex.get N w r))

private theorem labelWord_consistent {I : Type u} {ell N : ℕ}
    (label : I → CompleteWord ell) (beta : Profile ell)
    (w : PowIndex I N) :
    ApproxConsistent id beta 0 (labelWord label w) ↔
      ApproxConsistent label beta 0 w := by
  simp only [ApproxConsistent, wordCount, labelWord, PowIndex.get_ofFun, id_eq]

private theorem labelWord_reindex {I : Type u} {ell N : ℕ}
    (label : I → CompleteWord ell) (w : PowIndex I N)
    (e : Equiv.Perm (Fin N)) :
    labelWord label (PowIndex.reindex e w) = PowIndex.reindex e (labelWord label w) := by
  apply (PowIndex.equivFun (CompleteWord ell) N).injective
  funext r
  change PowIndex.get N (labelWord label (PowIndex.reindex e w)) r =
    PowIndex.get N (PowIndex.reindex e (labelWord label w)) r
  simp only [labelWord, PowIndex.get_ofFun, PowIndex.get_reindex]

/-- Actual coordinate bases, full-label blocks, and common uniform shuffles
for one exact complete-profile restricted tensor power. -/
theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {I : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i)) {ell : ℕ}
    (label : ∀ i, I i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (N : ℕ) :
    let Coord := fun i ↦ {w : PowIndex (I i) N // ApproxConsistent (label i) (beta i) 0 w}
    let Block := fun i ↦ {w : PowIndex (CompleteWord ell) N // ApproxConsistent id (beta i) 0 w}
    let S := restrictedPower T b label beta 0 N
    let G := (T.kronPow N).basisAllAllowedGrading
      (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) 0)
    ∃ B : ∀ i, Basis (Coord i) K (S.V i),
    ∃ blockLabel : ∀ i, Coord i → Block i,
    ∃ system : ∀ i, AvailableBlockShuffle (Block i) (Equiv.Perm (Fin N)),
      (∀ i w, (G.classOf i 0).subtype (B i w) = kronPowModeBasis T i (b i) N w.1) ∧
      (∀ i w, (blockLabel i w).1 =
        PowIndex.ofFun N (fun r ↦ label i (PowIndex.get N w.1 r))) ∧
      (∀ e i source, ((system i).move e source).1 = PowIndex.reindex e.symm source.1) ∧
      ∀ e : Equiv.Perm (Fin N),
        ∃ Ψ : ∀ i, S.V i ≃ₗ[K] S.V i,
        ∃ basisImage : ∀ i, Coord i → Coord i,
          PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap) S.t = S.t ∧
          (∀ i w, (basisImage i w).1 = PowIndex.reindex e.symm w.1) ∧
          (∀ i w, Ψ i (B i w) = B i (basisImage i w)) ∧
          (∀ i w, blockLabel i (basisImage i w) = (system i).move e (blockLabel i w)) := by
  classical
  let Coord := fun i ↦ {w : PowIndex (I i) N // ApproxConsistent (label i) (beta i) 0 w}
  let Block := fun i ↦ {w : PowIndex (CompleteWord ell) N // ApproxConsistent id (beta i) 0 w}
  let S := restrictedPower T b label beta 0 N
  let G := (T.kronPow N).basisAllAllowedGrading
    (fun i ↦ kronPowModeBasis T i (b i) N)
    (fun i ↦ ApproxConsistent (label i) (beta i) 0)
  have hbases (i : Fin 3) : ∃ B : Basis (Coord i) K (S.V i),
      ∀ w, (G.classOf i 0).subtype (B w) = kronPowModeBasis T i (b i) N w.1 :=
    allowed_basis_exists (T.kronPow N) (fun i ↦ kronPowModeBasis T i (b i) N)
      (fun i ↦ ApproxConsistent (label i) (beta i) 0) i
  choose B hB using hbases
  let blockLabel : ∀ i, Coord i → Block i := fun i w ↦
    ⟨labelWord (label i) w.1, (labelWord_consistent (label i) (beta i) w.1).2 w.2⟩
  have hsystems (i : Fin 3) : ∃ system : AvailableBlockShuffle (Block i) (Equiv.Perm (Fin N)),
      ∀ e source, (system.move e source).1 = PowIndex.reindex e.symm source.1 :=
    mme_complete_split_exact_type_uniform_chunk_shuffle ell (beta i) N
  choose system hsystem using hsystems
  refine ⟨B, blockLabel, system, hB, fun _ _ ↦ rfl, ?_, ?_⟩
  · intro e i source
    exact hsystem i e source
  · intro e
    obtain ⟨hcounts, Ψ, ht, hinc⟩ :=
      mme_complete_split_restrictedPower_chunk_symmetry T b label beta 0 N e.symm
    let basisImage : ∀ i, Coord i → Coord i := fun i w ↦
      ⟨PowIndex.reindex e.symm w.1, by
        simpa only [ApproxConsistent, hcounts] using w.2⟩
    refine ⟨Ψ, basisImage, ht, fun _ _ ↦ rfl, ?_, ?_⟩
    · intro i w
      apply Subtype.val_injective
      have hi := LinearMap.congr_fun (hinc i) (B i w)
      simp only [LinearMap.comp_apply] at hi
      calc
        _ = kronPowModePositionEquiv T i (b i) N e.symm
            ((G.classOf i 0).subtype (B i w)) := hi
        _ = kronPowModePositionEquiv T i (b i) N e.symm
            (kronPowModeBasis T i (b i) N w.1) := by rw [hB]
        _ = kronPowModeBasis T i (b i) N (PowIndex.reindex e.symm w.1) :=
          mme_kronPow_position_permutation_recursive_basis T i (b i) N e.symm w.1
        _ = _ := (hB i (basisImage i w)).symm
    · intro i w
      apply Subtype.ext
      change labelWord (label i) (PowIndex.reindex e.symm w.1) =
        ((system i).move e (blockLabel i w)).1
      rw [hsystem]
      exact labelWord_reindex (label i) w.1 e.symm
