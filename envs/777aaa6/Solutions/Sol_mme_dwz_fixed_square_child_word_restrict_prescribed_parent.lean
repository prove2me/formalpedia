-- Prove2me | solution 1 for mme_dwz_fixed_square_child_word_restrict_prescribed_parent
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:05:07.885468+00:00
-- url     : https://prove2.me/submissions/7d9b44b9-8fbe-496e-a7f3-83c23fdffd5c

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_complete_split_cw_fourth_label_certificate
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Definitions.Def_mme_dwz_prescribed_z_split_value

open MME MME.TensorObj MME.TensorObj.TypeGrading MME.StothersFourth
  MME.CompleteSplit.CWFourth MME.DWZComponentRestriction MME.DWZRestrictedValue
  Module TensorProduct PiTensorProduct
open scoped Classical
universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

namespace MME.DWZC1ChildExtraction

theorem square_basis_mem {K : Type u} [Field K] (q : ℕ) (i : Fin 3)
    (a : Fin (q + 2) × Fin (q + 2)) :
    cwSquareCanonicalBasis K q i a ∈
      (cwSquareCanonicalGrading K q).classOf i (cwSquarePairGrade q a) := by
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

theorem fourth_basis_mem {K : Type u} [Field K] (q : ℕ) (i : Fin 3)
    (a : Coordinate q) :
    cwFourthCanonicalBasis K q i a ∈
      (cwFourthCanonicalGrading K q).classOf i (cwFourthPairGrade q a) := by
  exact Submodule.subset_span ⟨a, rfl, rfl⟩

noncomputable def pairProjection {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (sx sy : Fin 3 → Fin 5) (i : Fin 3) :
    (cwFourthConstituent K q I J L).V i →ₗ[K]
      (kron ((cwSquareCanonicalGrading K q).blockSubtensor sx)
        ((cwSquareCanonicalGrading K q).blockSubtensor sy)).V i :=
  (TensorProduct.map
    ((cwSquareCanonicalGrading K q).blockProj i (sx i))
    ((cwSquareCanonicalGrading K q).blockProj i (sy i))).comp
    ((cwFourthCanonicalGrading K q).classOf i (cwFourthBlockType I J L i)).subtype

theorem pairProjection_comp_coarse {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ i, (sx i).val + (sy i).val = (cwFourthBlockType I J L i).val)
    (i : Fin 3) :
    (pairProjection q I J L sx sy i).comp
      ((cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i)) =
    TensorProduct.map
      ((cwSquareCanonicalGrading K q).blockProj i (sx i))
      ((cwSquareCanonicalGrading K q).blockProj i (sy i)) := by
  apply (cwFourthCanonicalBasis K q i).ext
  rintro ⟨a,b⟩
  let G := cwFourthCanonicalGrading K q
  let F := TensorProduct.map
    ((cwSquareCanonicalGrading K q).blockProj i (sx i))
    ((cwSquareCanonicalGrading K q).blockProj i (sy i))
  change F ((G.blockProj i (cwFourthBlockType I J L i)
      (cwFourthCanonicalBasis K q i (a,b)) : G.classOf i _).val) =
    F (cwFourthCanonicalBasis K q i (a,b))
  by_cases hc : cwFourthPairGrade q (a,b) = cwFourthBlockType I J L i
  · rw [blockProj_apply_mem G i _ _ (hc ▸ fourth_basis_mem q i (a,b))]
  · rw [blockProj_apply_mem_ne G i _ (cwFourthPairGrade q (a,b))
      (Ne.symm hc) _ (fourth_basis_mem q i (a,b))]
    change F 0 = F (cwFourthCanonicalBasis K q i (a,b))
    rw [map_zero]
    unfold cwFourthCanonicalBasis
    erw [Basis.tensorProduct_apply]
    dsimp only [F]
    rw [TensorProduct.map_tmul]
    by_cases ha : cwSquarePairGrade q a = sx i
    · have hb : cwSquarePairGrade q b ≠ sy i := by
        intro hb
        apply hc
        apply Fin.ext
        change (cwSquarePairGrade q a).val + (cwSquarePairGrade q b).val = _
        rw [ha,hb]
        exact hsum i
      rw [blockProj_apply_mem_ne _ i _ _ (Ne.symm hb) _ (square_basis_mem q i b)]
      simp only [tmul_zero]
    · rw [blockProj_apply_mem_ne _ i _ _ (Ne.symm ha) _ (square_basis_mem q i a)]
      simp only [zero_tmul]

theorem pairProjection_tensor {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (sx sy : Fin 3 → Fin 5)
    (hsum : ∀ i, (sx i).val + (sy i).val = (cwFourthBlockType I J L i).val) :
    PiTensorProduct.map (pairProjection q I J L sx sy)
      (cwFourthConstituent K q I J L).t =
    (kron ((cwSquareCanonicalGrading K q).blockSubtensor sx)
      ((cwSquareCanonicalGrading K q).blockSubtensor sy)).t := by
  change PiTensorProduct.map (pairProjection q I J L sx sy)
    (PiTensorProduct.map (fun i ↦ (cwFourthCanonicalGrading K q).blockProj i
      (cwFourthBlockType I J L i)) (cwFourthObj K q).t) = _
  have hcomp := LinearMap.congr_fun
    (PiTensorProduct.map_comp (pairProjection q I J L sx sy)
      (fun i ↦ (cwFourthCanonicalGrading K q).blockProj i
        (cwFourthBlockType I J L i))) (cwFourthObj K q).t
  erw [← hcomp]
  have heq := funext (pairProjection_comp_coarse (K := K) q I J L sx sy hsum)
  rw [heq]
  exact kronMap_interchange _ _ _ _

theorem pairProjection_basis_zero {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (sx sy : Fin 3 → Fin 5) (i : Fin 3)
    (a : LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i))
    (h : cwSquarePairGrade q a.down.val.1 ≠ sx i) :
    pairProjection q I J L sx sy i (constituentBasis K q I J L i a) = 0 := by
  unfold pairProjection
  erw [LinearMap.comp_apply]
  change TensorProduct.map ((cwSquareCanonicalGrading K q).blockProj i (sx i))
    ((cwSquareCanonicalGrading K q).blockProj i (sy i))
      (constituentBasis K q I J L i a).val = 0
  rw [(mme_complete_split_cw_fourth_label_certificate (K := K) q I J L).1 i a]
  unfold cwFourthCanonicalBasis
  erw [Basis.tensorProduct_apply]
  rw [TensorProduct.map_tmul]
  rw [blockProj_apply_mem_ne _ i _ _ (Ne.symm h) _
    (square_basis_mem q i a.down.val.1)]
  exact zero_tmul _ _

set_option linter.unusedVariables false in
noncomputable def powerToFamily {K : Type u} [Field K] (T : TensorObj K 3) :
    ∀ n (Y : Fin n → TensorObj K 3)
      (f : ∀ r i, T.V i →ₗ[K] (Y r).V i) (i : Fin 3),
      (T.kronPow n).V i →ₗ[K] (kronFin n Y).V i
  | 0, _, _, _ => LinearMap.id
  | n+1, Y, f, i => TensorProduct.map (f 0 i)
      (powerToFamily T n (fun r ↦ Y r.succ) (fun r j ↦ f r.succ j) i)

theorem powerToFamily_tensor {K : Type u} [Field K] (T : TensorObj K 3)
    (n : ℕ) (Y : Fin n → TensorObj K 3)
    (f : ∀ r i, T.V i →ₗ[K] (Y r).V i)
    (hf : ∀ r, PiTensorProduct.map (f r) T.t = (Y r).t) :
    PiTensorProduct.map (powerToFamily T n Y f) (T.kronPow n).t =
      (kronFin n Y).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ : Fin 3 ↦ LinearMap.id) _ = _
      rw [PiTensorProduct.map_id]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (f 0 i)
          (powerToFamily T n (fun r ↦ Y r.succ) (fun r j ↦ f r.succ j) i))
        (interchange T.t (T.kronPow n).t) = _
      rw [kronMap_interchange, hf 0,
        ih (fun r ↦ Y r.succ) (fun r j ↦ f r.succ j) (fun r ↦ hf r.succ)]
      rfl

theorem powerToFamily_basis_zero {K : Type u} [Field K] (T : TensorObj K 3)
    (n : ℕ) (Y : Fin n → TensorObj K 3)
    (f : ∀ r i, T.V i →ₗ[K] (Y r).V i) (i : Fin 3)
    {ι : Type u} (b : Basis ι K (T.V i)) (w : PowIndex ι n)
    (hzero : ∃ r, f r i (b (PowIndex.get n w r)) = 0) :
    powerToFamily T n Y f i (kronPowModeBasis T i b n w) = 0 := by
  induction n with
  | zero => rcases hzero with ⟨r,_⟩; exact r.elim0
  | succ n ih =>
      change TensorProduct.map (f 0 i)
        (powerToFamily T n (fun r ↦ Y r.succ) (fun r j ↦ f r.succ j) i)
        (b.tensorProduct (kronPowModeBasis T i b n) w) = 0
      erw [Basis.tensorProduct_apply, TensorProduct.map_tmul]
      rcases hzero with ⟨r,hr⟩
      revert hr
      refine Fin.cases ?_ (fun r ↦ ?_) r
      · intro h0
        change f 0 i (b w.1) = 0 at h0
        rw [h0, zero_tmul]
      · intro hr
        have htail := ih (fun r ↦ Y r.succ) (fun r j ↦ f r.succ j) w.2 ⟨r,hr⟩
        rw [htail, tmul_zero]

/-- A fixed ordered word of square-child pairs survives the literal prescribed
parent Z projection exactly when its left-square histogram is prescribed. -/
theorem fixed_child_word_restrict {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5)
    (hsum : ∀ r i, (sx r i).val + (sy r i).val = (cwFourthBlockType I J L i).val)
    (hprofile : ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (p.length m) ↦ sx r 2 = a)).card = p.count a*m) :
    TensorObj.Restrict
      (kronFin (p.length m) (fun r ↦
        kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
          ((cwSquareCanonicalGrading K q).blockSubtensor (sy r))))
      (prescribedZPower (cwFourthConstituent K q I J L)
        (constituentBasis K q I J L 2)
        (fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1)
        p m) := by
  classical
  let T := cwFourthConstituent K q I J L
  let Y := fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
    ((cwSquareCanonicalGrading K q).blockSubtensor (sy r))
  let f := fun r ↦ pairProjection (K := K) q I J L (sx r) (sy r)
  apply mme_restrict_basisZAllowedSubtensor_of_vanishes (T.kronPow (p.length m))
    (kronFin (p.length m) Y)
    (kronPowModeBasis T 2 (constituentBasis K q I J L 2) (p.length m))
    (prescribedZWord (fun a : LiftedCoarseCoordinate.{u} q L ↦
      cwSquarePairGrade q a.down.val.1) p m)
    (powerToFamily T (p.length m) Y f)
  · exact powerToFamily_tensor T (p.length m) Y f
      (fun r ↦ pairProjection_tensor q I J L (sx r) (sy r) (hsum r))
  · intro w hw
    apply powerToFamily_basis_zero
    have hbad : ∃ r, cwSquarePairGrade q (PowIndex.get (p.length m) w r).down.val.1 ≠
        sx r 2 := by
      by_contra h
      push_neg at h
      apply hw
      intro a
      unfold leftGradeCount
      have heq : (Finset.univ.filter (fun r : Fin (p.length m) ↦
          cwSquarePairGrade q (PowIndex.get (p.length m) w r).down.val.1 = a)) =
          Finset.univ.filter (fun r : Fin (p.length m) ↦ sx r 2 = a) := by
        apply Finset.filter_congr
        intro r _
        rw [h r]
      exact (congrArg Finset.card heq).trans (hprofile a)
    rcases hbad with ⟨r,hr⟩
    exact ⟨r, pairProjection_basis_zero q I J L (sx r) (sy r) 2 _ hr⟩

end MME.DWZC1ChildExtraction

theorem solution {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5)
    (hsum : ∀ r i, (sx r i).val + (sy r i).val = (cwFourthBlockType I J L i).val)
    (hprofile : ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (p.length m) ↦ sx r 2 = a)).card = p.count a*m) :
    TensorObj.Restrict
      (kronFin (p.length m) (fun r ↦
        kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
          ((cwSquareCanonicalGrading K q).blockSubtensor (sy r))))
      (prescribedZPower (cwFourthConstituent K q I J L)
        (constituentBasis K q I J L 2)
        (fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1)
        p m) := by
  exact MME.DWZC1ChildExtraction.fixed_child_word_restrict q I J L p m sx sy hsum hprofile
