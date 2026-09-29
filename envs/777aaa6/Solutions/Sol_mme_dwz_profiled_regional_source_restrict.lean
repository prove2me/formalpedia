-- Prove2me | solution 1 for mme_dwz_profiled_regional_source_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-21T07:04:55.946761+00:00
-- url     : https://prove2.me/submissions/4338ae33-a25c-4eba-b7cb-f75af93b1617

import Definitions.Def_mme_dwz_profiled_regional_keep_data
import Definitions.Def_mme_stothers_fourth_data
import Definitions.Def_mme_complete_split_cw_fourth_labels
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_recursive_profiled_CW_data
import Definitions.Def_mme_tensor_quotient
import Theorems.Thm_mme_CW_atomic_fourth_component_grouping_projection_transport
import Theorems.Thm_mme_CW_fourth_component_profile_projection_normalization
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes
import Definitions.Def_mme_TypeGrading_kron

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.CompleteSplit
  MME.StothersFourth MME.DWZRestrictedValue MME.DWZComponentRestriction
  MME.CompleteSplit.CWFourth MME.DWZProfiledRegional
  Module PiTensorProduct
open scoped Classical

universe u

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace MME.DWZProfiledRegionalSource

/-- Invert a restriction whose maps are linear equivalences. -/
private theorem restrict_symm {K : Type u} [Field K] {d : ℕ} {X Y : TensorObj K d}
    (f : ∀ i, Y.V i ≃ₗ[K] X.V i)
    (hf : PiTensorProduct.map (fun i ↦ (f i).toLinearMap) Y.t = X.t) :
    TensorObj.Restrict Y X := by
  refine ⟨fun i ↦ (f i).symm.toLinearMap, ?_⟩
  -- `map_comp` composes linear maps, so fold the application into a composition first
  rw [← hf, ← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  have hid : (fun i ↦ ((f i).symm.toLinearMap ∘ₗ (f i).toLinearMap)) =
      fun i ↦ (LinearMap.id : Y.V i →ₗ[K] Y.V i) := by
    funext i
    exact LinearMap.ext fun y ↦ (f i).symm_apply_apply y
  rw [hid, PiTensorProduct.map_id, LinearMap.id_apply]

/-- `ProfiledCW.tensor` unfolded, stated generically.  Proving this with `P` and `N` as
variables is immediate; asking the elaborator for the same equality on the concrete `dwzKeep`
term instead makes it normalize spans and submodules, which does not finish. -/
private theorem tensor_eq_subtensor {K : Type u} [Field K] {N : ℕ}
    (P : ProfiledCW.Predicate N) :
    ProfiledCW.tensor K P =
      ((CWObj K 5).kronPow N).basisAllAllowedSubtensor (ProfiledCW.canonical K N)
        (fun i x ↦ P i (ProfiledCW.fine x)) := rfl

/-- `restrict_symm` for the two basis subtensors `ae8ae0cb` relates.  Every argument is read off
`f`'s type by first-order matching, so no tensor value is ever compared. -/
private theorem restrict_of_subtensor_equiv {K : Type u} [Field K]
    {T U : TensorObj K 3} {ι κ : Fin 3 → Type u}
    {B : (i : Fin 3) → Basis (ι i) K (T.V i)} {D : (i : Fin 3) → Basis (κ i) K (U.V i)}
    {P : (i : Fin 3) → ι i → Prop} {Q : (i : Fin 3) → κ i → Prop}
    (f : ∀ i, (T.basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K]
        (U.basisAllAllowedGrading D Q).classOf i 0)
    (hf : PiTensorProduct.map (fun i ↦ (f i).toLinearMap) (T.basisAllAllowedSubtensor B P).t =
        (U.basisAllAllowedSubtensor D Q).t) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor B P) (U.basisAllAllowedSubtensor D Q) :=
  restrict_symm f hf

/-- The same for a subtensor presented as `blockSubtensor` of its grading, as `e9fa2224` does. -/
private theorem restrict_of_grading_equiv {K : Type u} [Field K]
    {T S : TensorObj K 3} {ι : Fin 3 → Type u}
    {B : (i : Fin 3) → Basis (ι i) K (T.V i)} {P : (i : Fin 3) → ι i → Prop}
    (F : ∀ i, (T.basisAllAllowedGrading B P).classOf i 0 ≃ₗ[K] S.V i)
    (hF : PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        ((T.basisAllAllowedGrading B P).blockSubtensor (fun _ ↦ 0)).t = S.t) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor B P) S :=
  restrict_symm F hF

/-- Shrinking the allowed set restricts: project onto the smaller subtensor, which kills every
basis vector outside the larger allowed set. -/
private theorem restrict_sub_of_imp {K : Type u} [Field K]
    {T : TensorObj K 3} {ι : Fin 3 → Type u}
    {B : (i : Fin 3) → Basis (ι i) K (T.V i)} {P P' : (i : Fin 3) → ι i → Prop}
    (himp : ∀ i w, P i w → P' i w) :
    TensorObj.Restrict (T.basisAllAllowedSubtensor B P) (T.basisAllAllowedSubtensor B P') := by
  classical
  refine mme_restrict_basisAllAllowedSubtensor_of_vanishes T (T.basisAllAllowedSubtensor B P) B P'
    (fun i ↦ (T.basisAllAllowedGrading B P).blockProj i 0) rfl ?_
  intro i j hj
  refine TensorObj.TypeGrading.blockProj_apply_mem_ne _ i 0 1 (by decide) _ ?_
  have hn : ¬ P i j := fun h ↦ hj (himp i j h)
  exact Submodule.subset_span ⟨j, by simp [hn], rfl⟩

/-- The bookkeeping content of Lemma B: an atomic word kept by `dwzKeep` groups into a word
satisfying `e9fa2224`'s per-region predicate.  Stated over variables, so nothing concrete unfolds. -/
private theorem keep_imp {R L N : ℕ} (I J Lz : Fin R → Fin 9)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ) (parent : Fin R → Fin 3 → ℕ)
    (hparent : ∀ r i, parent r i = (cwFourthBlockType (I r) (J r) (Lz r) i).val)
    (keptMode : Fin R → Fin 3) (hkept : ∀ r, keptMode r = 2)
    (positions : Fin L ≃ Position (fun r ↦ (p r).length (scale r)))
    (length : L * 2 ^ (2 - 1) = N * 4)
    (group : Fin N ≃ (Σ r : Fin R, Fin ((p r).length (scale r))))
    (hcompat : ∀ (u : Fin N) (s k : Fin 2),
      Fin.cast length (finProdFinEquiv (positions.symm ⟨(group u).1, (group u).2, s⟩, k)) =
        Fin.cast rfl (finProdFinEquiv (u, finProdFinEquiv (s, k))))
    (e : (Fin (N * 4) → ULift.{u, 0} (Fin (5 + 2))) ≃
      ((c : Fin R) → Fin ((p c).length (scale c)) →
        ULift.{u, 0} ((Fin (5 + 2) × Fin (5 + 2)) × Fin (5 + 2) × Fin (5 + 2))))
    (hgrade4 : ∀ w c r, (cwFourthPairGrade 5 (e w c r).down).val =
      ∑ s : Fin 4, (DWZSimultaneous.label 5 3 N w (group.symm ⟨c, r⟩) s).val)
    (hgradeL : ∀ w c r, cwSquarePairGrade 5 (e w c r).down.1 =
      DWZSimultaneous.fourthLeftTag (DWZSimultaneous.label 5 3 N w (group.symm ⟨c, r⟩)))
    (i : Fin 3) (w : (c : Fin R) → Fin ((p c).length (scale c)) →
        ULift.{u, 0} ((Fin (5 + 2) × Fin (5 + 2)) × Fin (5 + 2) × Fin (5 + 2)))
    (hkeep : dwzKeep parent (fun r ↦ (p r).length (scale r)) keptMode p scale positions length i
      (ProfiledCW.fine (e.symm w)))
    (r : Fin R) :
    (∀ t, cwFourthPairGrade 5 (w r t).down = cwFourthBlockType (I r) (J r) (Lz r) i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter (fun t ↦ cwSquarePairGrade 5 (w r t).down.1 = a)).card =
          (p r).count a * scale r) := by
  classical
  obtain ⟨hk1, hk2⟩ := hkeep
  -- where the two halves of slot `(r, t)` sit in the atomic word
  have hc : ∀ (t : Fin ((p r).length (scale r))) (s k : Fin 2),
      Fin.cast length (finProdFinEquiv (positions.symm ⟨r, t, s⟩, k)) =
        finProdFinEquiv (group.symm ⟨r, t⟩, finProdFinEquiv (s, k)) := by
    intro t s k
    have h := hcompat (group.symm ⟨r, t⟩) s k
    rw [Equiv.apply_symm_apply, Fin.cast_eq_self] at h
    exact h
  have hsplit : ∀ (t : Fin ((p r).length (scale r))) (s k : Fin 2),
      (ProfiledCW.split (ell := 2) positions length (ProfiledCW.fine (e.symm w)) ⟨r, t, s⟩ k).val =
        (ProfiledCW.fine (e.symm w) (finProdFinEquiv (group.symm ⟨r, t⟩, finProdFinEquiv (s, k)))).val := by
    intro t s k
    unfold ProfiledCW.split
    rw [hc t s k]
  have hlabel : ∀ (t : Fin ((p r).length (scale r))) (s : Fin 4),
      (DWZSimultaneous.label 5 3 N (e.symm w) (group.symm ⟨r, t⟩) s).val =
        (ProfiledCW.fine (e.symm w) (finProdFinEquiv (group.symm ⟨r, t⟩, s))).val :=
    fun _ _ ↦ rfl
  -- the four atomic grades of a slot are the grades of its two halves
  have hsum : ∀ t : Fin ((p r).length (scale r)),
      ∑ s : Fin 4, (DWZSimultaneous.label 5 3 N (e.symm w) (group.symm ⟨r, t⟩) s).val =
        CWCells.grade (ProfiledCW.split (ell := 2) positions length (ProfiledCW.fine (e.symm w)) ⟨r, t, 0⟩) +
          CWCells.grade (ProfiledCW.split (ell := 2) positions length (ProfiledCW.fine (e.symm w)) ⟨r, t, 1⟩) := by
    intro t
    simp only [CWCells.grade, hlabel, hsplit]
    have key : ∑ q : Fin 2 × Fin 2,
        (ProfiledCW.fine (e.symm w) (finProdFinEquiv (group.symm ⟨r, t⟩, finProdFinEquiv q))).val =
          ∑ s : Fin 4, (ProfiledCW.fine (e.symm w) (finProdFinEquiv (group.symm ⟨r, t⟩, s))).val :=
      Fintype.sum_equiv finProdFinEquiv _ _ (fun _ ↦ rfl)
    rw [← key, Fintype.sum_prod_type, Fin.sum_univ_two]
    rfl
  -- the left square grade of a slot is the grade of its left half
  have hleft : ∀ t : Fin ((p r).length (scale r)),
      (DWZSimultaneous.fourthLeftTag (DWZSimultaneous.label 5 3 N (e.symm w) (group.symm ⟨r, t⟩))).val =
        CWCells.grade (ProfiledCW.split (ell := 2) positions length (ProfiledCW.fine (e.symm w)) ⟨r, t, 0⟩) := by
    intro t
    simp only [CWCells.grade, hsplit]
    rfl
  refine ⟨fun t ↦ ?_, fun hi a ↦ ?_⟩
  · apply Fin.ext
    have h4 := hgrade4 (e.symm w) r t
    rw [Equiv.apply_symm_apply] at h4
    exact h4.trans ((hsum t).trans ((hk1 r t).trans (hparent r i)))
  · rw [← hk2 r (hi.trans (hkept r).symm) a]
    refine congrArg Finset.card (Finset.filter_congr fun t _ ↦ ?_)
    have hL := hgradeL (e.symm w) r t
    rw [Equiv.apply_symm_apply] at hL
    rw [hL, Fin.ext_iff, hleft t]

end MME.DWZProfiledRegionalSource

open MME.DWZProfiledRegionalSource

theorem solution {K : Type u} [Field K] {R L M N : ℕ}
    (I J Lz : Fin R → Fin 9)
    (p : Fin R → IntegerZSplitProfile 5) (scale : Fin R → ℕ)
    (parent : Fin R → Fin 3 → ℕ)
    (hparent : ∀ r i, parent r i = (cwFourthBlockType (I r) (J r) (Lz r) i).val)
    (keptMode : Fin R → Fin 3) (hkept : ∀ r, keptMode r = 2)
    (n : Fin R → ℕ) (hn : n = fun r ↦ (p r).length (scale r))
    (positions : Fin L ≃ Position n) (length : L * 2 ^ (2 - 1) = M)
    (group : Fin N ≃ (Σ r : Fin R, Fin (n r))) (hM : N * 4 = M)
    (hcompat : ∀ (u : Fin N) (s k : Fin 2),
      Fin.cast length (finProdFinEquiv (positions.symm ⟨(group u).1, (group u).2, s⟩, k)) =
        Fin.cast hM (finProdFinEquiv (u, finProdFinEquiv (s, k)))) :
    TensorObj.Restrict
      (ProfiledCW.tensor K (dwzKeep parent n keptMode p scale positions length))
      (kronFin R (fun r ↦
        prescribedZPower (cwFourthConstituent K 5 (I r) (J r) (Lz r))
          (constituentBasis K 5 (I r) (J r) (Lz r) 2)
          (fun a : LiftedCoarseCoordinate.{u} 5 (Lz r) ↦ cwSquarePairGrade 5 a.down.val.1)
          (p r) (scale r))) := by
  classical
  -- put `n` in the shape `e9fa2224` uses, so nothing has to be transported later
  subst hM
  subst hn
  -- STEP 1: regroup the four atomic slots of each fourth-power position.
  obtain ⟨e, he, Phi, hPhiT, hPhiB, hgrade4, hgradeL, hproj⟩ :=
    mme_CW_atomic_fourth_component_grouping_projection_transport (K := K) 5
      (fun r ↦ (p r).length (scale r)) group
  obtain ⟨f, hft, hfb, hfx⟩ :=
    hproj (fun i x ↦ dwzKeep parent (fun r ↦ (p r).length (scale r)) keptMode p scale
      positions length i (ProfiledCW.fine x))
  obtain ⟨beta, hbeta, F, hFt, hFb⟩ :=
    mme_CW_fourth_component_profile_projection_normalization (K := K) 5 I J Lz p scale
  -- `ProfiledCW.tensor K dwzKeep` is, by definition, the atomic subtensor `ae8ae0cb` regroups
  rw [tensor_eq_subtensor]
  -- regroup (ae8ae0cb), shrink the allowed set to e9fa2224's predicate, then normalize (e9fa2224)
  have h1 := restrict_of_subtensor_equiv f hft
  have h3 := restrict_of_grading_equiv F hFt
  refine h1.trans (TensorObj.Restrict.trans (restrict_sub_of_imp ?_) h3)
  intro i w hw r
  exact keep_imp I J Lz p scale parent hparent keptMode hkept positions length group hcompat e
    hgrade4 hgradeL i w hw r
