-- Prove2me | solution 1 for mme_dwz_induced_regional_square_children_restrict_original_profiles
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-18T15:54:54.982988+00:00
-- url     : https://prove2.me/submissions/a4ebc3e1-a9c2-408d-8be3-6456cb87fe44

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_complete_split_cw_fourth_label_certificate
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_induced_word_zeroing
import Definitions.Def_mme_permutation
import Theorems.Thm_mme_CW_square_canonical_support_and_scalar_blocks
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

open MME MME.TensorObj MME.TensorObj.TypeGrading MME.StothersFourth
  MME.CompleteSplit.CWFourth MME.DWZComponentRestriction MME.DWZRestrictedValue
  Module TensorProduct PiTensorProduct BigOperators
open scoped Classical
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 150000

namespace MME.DWZC1SimultaneousChild

open DWZC1ChildExtraction

/-- The literal inclusion of the selected profile mode spaces followed by the
already constructed maps.  It preserves their action whenever they kill every
forbidden Z basis vector. -/
theorem map_from_Z_projection {K : Type u} [Field K]
    (T : TensorObj K 3) {ι : Type u} (b : Basis ι K (T.V 2))
    (allowed : ι → Prop) [DecidablePred allowed]
    {W : Fin 3 → Type u} [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, T.V i →ₗ[K] W i)
    (hvanish : ∀ j, ¬ allowed j → f 2 (b j) = 0) :
    PiTensorProduct.map
      (fun i ↦ (f i).comp ((T.basisZAllowedGrading b allowed).classOf i 0).subtype)
      (T.basisZAllowedSubtensor b allowed).t = PiTensorProduct.map f T.t := by
  have hinc := mme_basisZAllowed_blockSubtensor_inclusion_tensor T b allowed
  change PiTensorProduct.map
      (fun i ↦ ((T.basisZAllowedGrading b allowed).classOf i 0).subtype)
      (T.basisZAllowedSubtensor b allowed).t = _ at hinc
  rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
  rw [hinc]
  rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
  apply congrArg (fun maps ↦ PiTensorProduct.map maps T.t)
  funext i
  by_cases hi : i = 2
  · subst i
    rw [Function.update_self]
    apply b.ext
    intro j
    simp only [LinearMap.comp_apply, Basis.constr_basis]
    by_cases h : allowed j
    · rw [if_pos h]
    · rw [if_neg h, map_zero, hvanish j h]
  · rw [Function.update_of_ne hi, LinearMap.comp_id]

/-- Mixed mode maps across a heterogeneous ordered product vanish if their
action on even one factor is zero. -/
theorem family_mixed_zero {K : Type u} [Field K] {R k : ℕ}
    (X : Fin R → TensorObj K 3) (Y : Fin k → Fin R → TensorObj K 3)
    (f : ∀ j r i, (X r).V i →ₗ[K] (Y j r).V i)
    (js : Fin 3 → Fin k) (r : Fin R)
    (hr : PiTensorProduct.map (fun i ↦ f (js i) r i) (X r).t = 0) :
    PiTensorProduct.map
      (fun i ↦ kronFinFamilyModeMap R X (Y (js i)) (f (js i)) i)
      (kronFin R X).t = 0 := by
  induction R with
  | zero => exact r.elim0
  | succ R ih =>
    refine Fin.cases ?_ (fun r ↦ ?_) r hr
    · intro h0
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (f (js i) 0 i)
          (kronFinFamilyModeMap R (fun r ↦ X r.succ)
            (fun r ↦ Y (js i) r.succ) (fun r h ↦ f (js i) r.succ h) i))
        (interchange (X 0).t (kronFin R (fun r ↦ X r.succ)).t) = 0
      rw [kronMap_interchange, h0]
      simp only [map_zero, LinearMap.zero_apply]
    · intro hr
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (f (js i) 0 i)
          (kronFinFamilyModeMap R (fun r ↦ X r.succ)
            (fun r ↦ Y (js i) r.succ) (fun r h ↦ f (js i) r.succ h) i))
        (interchange (X 0).t (kronFin R (fun r ↦ X r.succ)).t) = 0
      rw [kronMap_interchange]
      rw [ih (fun r ↦ X r.succ) (fun j r ↦ Y j r.succ)
        (fun j r i ↦ f j r.succ i) r hr]
      exact LinearMap.map_zero _

/-- Naturality permits independent regional rotations before assembly. -/
theorem rotated_mixed_zero {K : Type u} [Field K] {k : ℕ}
    (X : TensorObj K 3) (Y : Fin k → TensorObj K 3)
    (f : ∀ j i, X.V i →ₗ[K] (Y j).V i)
    (σ : Equiv.Perm (Fin 3)) (js : Fin 3 → Fin k)
    (hzero : PiTensorProduct.map (fun i ↦ f (js (σ i)) i) X.t = 0) :
    PiTensorProduct.map (fun i ↦ f (js i) (σ.symm i))
      (permObj σ X).t = 0 := by
  let g := fun i ↦ f (js (σ i)) i
  have h := PiTensorProduct.map_reindex (f := g) σ X.t
  dsimp only [g] at h
  rw [hzero, map_zero] at h
  let Q (s : Fin 3 → Fin k) : Prop :=
    PiTensorProduct.map (fun i ↦ f (s i) (σ.symm i)) (permObj σ X).t = 0
  change Q (fun i ↦ js (σ (σ.symm i))) at h
  have heq : (fun i ↦ js (σ (σ.symm i))) = js := by
    funext i
    rw [Equiv.apply_symm_apply]
  rw [heq] at h
  exact h

theorem mixed_pair_zero {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) {k : ℕ} (sx sy : Fin k → Fin 3 → Fin 5)
    (hsum : ∀ j i, (sx j i).val + (sy j i).val = (cwFourthBlockType I J L i).val)
    (js : Fin 3 → Fin k)
    (hzero : (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sx (js i) i) = 0 ∨
      (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sy (js i) i) = 0) :
    PiTensorProduct.map (fun i ↦ pairProjection q I J L (sx (js i)) (sy (js i)) i)
      (cwFourthConstituent K q I J L).t = 0 := by
  have h := pairProjection_tensor (K := K) q I J L
    (fun i ↦ sx (js i) i) (fun i ↦ sy (js i) i) (fun i ↦ hsum (js i) i)
  change PiTensorProduct.map (fun i ↦ pairProjection q I J L (sx (js i)) (sy (js i)) i)
      (cwFourthConstituent K q I J L).t =
    interchange ((cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sx (js i) i))
      ((cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sy (js i) i)) at h
  rw [h]
  rcases hzero with hzero | hzero
  · rw [hzero]
    simp only [map_zero, LinearMap.zero_apply]
    rfl
  · rw [hzero]
    simp only [map_zero]
    rfl

theorem mixed_power_zero {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) {N k : ℕ} (sx sy : Fin k → Fin N → Fin 3 → Fin 5)
    (hsum : ∀ j r i, (sx j r i).val + (sy j r i).val =
      (cwFourthBlockType I J L i).val)
    (js : Fin 3 → Fin k) (r : Fin N)
    (hzero : (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sx (js i) r i) = 0 ∨
      (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sy (js i) r i) = 0) :
    PiTensorProduct.map (fun i ↦ powerToFamily (cwFourthConstituent K q I J L) N
      (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx (js i) r))
        ((cwSquareCanonicalGrading K q).blockSubtensor (sy (js i) r)))
      (fun r ↦ pairProjection q I J L (sx (js i) r) (sy (js i) r)) i)
      ((cwFourthConstituent K q I J L).kronPow N).t = 0 := by
  induction N with
  | zero => exact r.elim0
  | succ N ih =>
    refine Fin.cases ?_ (fun r ↦ ?_) r hzero
    · intro h0
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (pairProjection q I J L (sx (js i) 0) (sy (js i) 0) i)
          (powerToFamily (cwFourthConstituent K q I J L) N
            (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx (js i) r.succ))
              ((cwSquareCanonicalGrading K q).blockSubtensor (sy (js i) r.succ)))
            (fun r ↦ pairProjection q I J L (sx (js i) r.succ) (sy (js i) r.succ)) i))
        (interchange (cwFourthConstituent K q I J L).t
          ((cwFourthConstituent K q I J L).kronPow N).t) = 0
      rw [kronMap_interchange,
        mixed_pair_zero q I J L (fun j ↦ sx j 0) (fun j ↦ sy j 0)
          (fun j i ↦ hsum j 0 i) js h0]
      simp only [map_zero, LinearMap.zero_apply]
    · intro hr
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (pairProjection q I J L (sx (js i) 0) (sy (js i) 0) i)
          (powerToFamily (cwFourthConstituent K q I J L) N
            (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx (js i) r.succ))
              ((cwSquareCanonicalGrading K q).blockSubtensor (sy (js i) r.succ)))
            (fun r ↦ pairProjection q I J L (sx (js i) r.succ) (sy (js i) r.succ)) i))
        (interchange (cwFourthConstituent K q I J L).t
          ((cwFourthConstituent K q I J L).kronPow N).t) = 0
      rw [kronMap_interchange,
        ih (fun j r ↦ sx j r.succ) (fun j r ↦ sy j r.succ)
          (fun j r i ↦ hsum j r.succ i) r hr]
      exact LinearMap.map_zero _

theorem power_pair_kills_bad_profile {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5)
    (hprofile : ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin (p.length m) ↦ sx r 2 = a)).card = p.count a*m)
    (w : PowIndex (LiftedCoarseCoordinate.{u} q L) (p.length m))
    (hw : ¬ prescribedZWord (fun a : LiftedCoarseCoordinate.{u} q L ↦
      cwSquarePairGrade q a.down.val.1) p m w) :
    powerToFamily (cwFourthConstituent K q I J L) (p.length m)
      (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
        ((cwSquareCanonicalGrading K q).blockSubtensor (sy r)))
      (fun r ↦ pairProjection q I J L (sx r) (sy r)) 2
      (kronPowModeBasis (cwFourthConstituent K q I J L) 2
        (constituentBasis K q I J L 2) (p.length m) w) = 0 := by
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

noncomputable def regionTarget {K : Type u} [Field K] (q N : ℕ)
    (sx sy : Fin N → Fin 3 → Fin 5) : TensorObj K 3 :=
  kronFin N (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
    ((cwSquareCanonicalGrading K q).blockSubtensor (sy r)))

noncomputable def regionSource {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ) : TensorObj K 3 :=
  prescribedZPower (cwFourthConstituent K q I J L)
    (constituentBasis K q I J L 2)
    (fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1) p m

noncomputable def regionMap {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5) (i : Fin 3) :
    (regionSource (K := K) q I J L p m).V i →ₗ[K]
      (regionTarget (K := K) q (p.length m) sx sy).V i :=
  (powerToFamily (cwFourthConstituent K q I J L) (p.length m)
    (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx r))
      ((cwSquareCanonicalGrading K q).blockSubtensor (sy r)))
    (fun r ↦ pairProjection q I J L (sx r) (sy r)) i).comp
    ((((cwFourthConstituent K q I J L).kronPow (p.length m)).basisZAllowedGrading
      (kronPowModeBasis (cwFourthConstituent K q I J L) 2
        (constituentBasis K q I J L 2) (p.length m))
      (prescribedZWord (fun a : LiftedCoarseCoordinate.{u} q L ↦
        cwSquarePairGrade q a.down.val.1) p m)).classOf i 0).subtype

theorem regionMap_mixed_eq {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ) {k : ℕ}
    (sx sy : Fin k → Fin (p.length m) → Fin 3 → Fin 5)
    (hprofile : ∀ j a, (Finset.univ.filter
      (fun r : Fin (p.length m) ↦ sx j r 2 = a)).card = p.count a*m)
    (js : Fin 3 → Fin k) :
    PiTensorProduct.map (fun i ↦ regionMap q I J L p m (sx (js i)) (sy (js i)) i)
      (regionSource q I J L p m).t =
    PiTensorProduct.map (fun i ↦ powerToFamily (cwFourthConstituent K q I J L) (p.length m)
      (fun r ↦ kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx (js i) r))
        ((cwSquareCanonicalGrading K q).blockSubtensor (sy (js i) r)))
      (fun r ↦ pairProjection q I J L (sx (js i) r) (sy (js i) r)) i)
      ((cwFourthConstituent K q I J L).kronPow (p.length m)).t := by
  apply map_from_Z_projection
  exact power_pair_kills_bad_profile q I J L p m (sx (js 2)) (sy (js 2)) (hprofile (js 2))

theorem regionMap_tensor {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ)
    (sx sy : Fin (p.length m) → Fin 3 → Fin 5)
    (hsum : ∀ r i, (sx r i).val + (sy r i).val = (cwFourthBlockType I J L i).val)
    (hprofile : ∀ a, (Finset.univ.filter
      (fun r : Fin (p.length m) ↦ sx r 2 = a)).card = p.count a*m) :
    PiTensorProduct.map (regionMap (K := K) q I J L p m sx sy)
      (regionSource (K := K) q I J L p m).t =
      (regionTarget (K := K) q (p.length m) sx sy).t := by
  rw [regionMap_mixed_eq q I J L p m (fun _ : Fin 1 ↦ sx) (fun _ ↦ sy)
    (fun _ ↦ hprofile) (fun _ ↦ 0)]
  exact powerToFamily_tensor _ _ _ _
    (fun r ↦ pairProjection_tensor q I J L (sx r) (sy r) (hsum r))

theorem regionMap_mixed_zero {K : Type u} [Field K] (q : ℕ)
    (I J L : Fin 9) (p : IntegerZSplitProfile 5) (m : ℕ) {k : ℕ}
    (sx sy : Fin k → Fin (p.length m) → Fin 3 → Fin 5)
    (hsum : ∀ j r i, (sx j r i).val + (sy j r i).val = (cwFourthBlockType I J L i).val)
    (hprofile : ∀ j a, (Finset.univ.filter
      (fun r : Fin (p.length m) ↦ sx j r 2 = a)).card = p.count a*m)
    (js : Fin 3 → Fin k) (r : Fin (p.length m))
    (hzero : (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sx (js i) r i) = 0 ∨
      (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sy (js i) r i) = 0) :
    PiTensorProduct.map (fun i ↦ regionMap (K := K) q I J L p m (sx (js i)) (sy (js i)) i)
      (regionSource (K := K) q I J L p m).t = 0 := by
  rw [regionMap_mixed_eq q I J L p m sx sy hprofile js]
  exact mixed_power_zero q I J L sx sy hsum js r hzero

/-- The two finite multilinearity identities used below are the explicit maps
from the accepted induced-address proof 587bf2c5-23d9-4298-be60-6b43795b823d. -/
theorem map_sum_modes {K : Type u} [Field K]
    {k : ℕ} {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (f : ∀ i, Fin k → V i →ₗ[K] W i) (x : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ ∑ j, f i j) x =
      ∑ js : Fin 3 → Fin k, PiTensorProduct.map (fun i ↦ f i (js i)) x := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    simp only [PiTensorProduct.map_tprod, LinearMap.coe_sum, Finset.sum_apply]
    rw [MultilinearMap.map_sum (PiTensorProduct.tprod K) _, Finset.smul_sum]
  | add x y ihx ihy =>
    simp only [map_add, ihx, ihy, Finset.sum_add_distrib]

theorem bigAdd_t_eq_sum_slot {K : Type u} [Field K] :
    ∀ (k : ℕ) (B : Fin k → TensorObj K 3),
      (bigAdd B).t = ∑ j : Fin k,
        PiTensorProduct.map (fun i ↦ gradedBigAddSlot k B j i) (B j).t
  | 0, _ => by
    change (zeroObj : TensorObj K 3).t = ∑ j : Fin 0, _
    simp only [Finset.univ_eq_empty, Finset.sum_empty]
    rfl
  | 1, B => by
    change (B 0).t = ∑ j : Fin 1,
      PiTensorProduct.map (fun i ↦ gradedBigAddSlot 1 B j i) (B j).t
    rw [Fin.sum_univ_one]
    change (B 0).t = PiTensorProduct.map (fun _ ↦ LinearMap.id) (B 0).t
    rw [PiTensorProduct.map_id]
    rfl
  | n+2, B => by
    change PiTensorProduct.map (fun i ↦ LinearMap.inl K ((B 0).V i)
        ((bigAdd (fun j ↦ B j.succ)).V i)) (B 0).t +
      PiTensorProduct.map (fun i ↦ LinearMap.inr K ((B 0).V i)
        ((bigAdd (fun j ↦ B j.succ)).V i)) (bigAdd (fun j ↦ B j.succ)).t =
      ∑ j : Fin (n+2), PiTensorProduct.map (fun i ↦ gradedBigAddSlot (n+2) B j i) (B j).t
    rw [Fin.sum_univ_succ, bigAdd_t_eq_sum_slot (n+1) (fun j ↦ B j.succ)]
    congr 1
    rw [map_sum]
    refine Finset.sum_congr rfl (fun j _ ↦ ?_)
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    rfl

theorem sum_slot_tensor {K : Type u} [Field K] {k : ℕ}
    (T : TensorObj K 3) (B : Fin k → TensorObj K 3)
    (f : ∀ j i, T.V i →ₗ[K] (B j).V i)
    (hdiag : ∀ j, PiTensorProduct.map (f j) T.t = (B j).t)
    (hoff : ∀ js : Fin 3 → Fin k, (¬ ∃ j, js = fun _ ↦ j) →
      PiTensorProduct.map (fun i ↦ f (js i) i) T.t = 0) :
    PiTensorProduct.map (fun i ↦ ∑ j, (gradedBigAddSlot k B j i).comp (f j i)) T.t =
      (bigAdd B).t := by
  classical
  rw [bigAdd_t_eq_sum_slot, map_sum_modes]
  let constChoice : Fin k → Fin 3 → Fin k := fun j _ ↦ j
  let diag : Finset (Fin 3 → Fin k) := Finset.univ.image constChoice
  have hzero : ∀ js : Fin 3 → Fin k, js ∉ diag →
      PiTensorProduct.map (fun i ↦ (gradedBigAddSlot k B (js i) i).comp (f (js i) i)) T.t = 0 := by
    intro js hjs
    have hn : ¬ ∃ j, js = fun _ ↦ j := by
      rintro ⟨j,rfl⟩
      exact hjs (Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩)
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hoff js hn, map_zero]
  calc
    _ = ∑ js ∈ diag,
        PiTensorProduct.map (fun i ↦ (gradedBigAddSlot k B (js i) i).comp (f (js i) i)) T.t := by
      symm
      apply Finset.sum_subset (by intro js _; exact Finset.mem_univ js)
      exact fun js _ hjs ↦ hzero js hjs
    _ = _ := by
      symm
      refine Finset.sum_bij (fun j (_ : j ∈ (Finset.univ : Finset (Fin k))) ↦ constChoice j)
        (fun j _ ↦ Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩) ?_ ?_ ?_
      · intro j₁ _ j₂ _ h
        exact congrFun h 0
      · intro js hjs
        obtain ⟨j,_,hj⟩ := Finset.mem_image.mp hjs
        exact ⟨j,Finset.mem_univ j,hj⟩
      · intro j _
        dsimp only [constChoice]
        rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hdiag j]

theorem square_nonzero_sum_four {K : Type u} [Field K] (q : ℕ) (s : Fin 3 → Fin 5)
    (h : (cwSquareCanonicalGrading K q).blockTensor s ≠ 0) :
    (s 0).val + (s 1).val + (s 2).val = 4 := by
  by_contra hsum
  have heq : cwSquareBlockType (s 0) (s 1) (s 2) = s := by
    funext i
    fin_cases i <;> rfl
  exact h (heq ▸ (mme_CW_square_canonical_support_and_scalar_blocks (K := K) q).1
    (s 0) (s 1) (s 2) hsum)

/-- Assemble all regions before diagonalization.  Each region retains its
original prescribed Z profile and then rotates the entire projected object.
One zero square block anywhere eliminates an off-diagonal global choice. -/
theorem simultaneous_regional_restrict {K : Type u} [Field K] (q R k : ℕ)
    (I J L : Fin R → Fin 9) (p : Fin R → IntegerZSplitProfile 5)
    (m : Fin R → ℕ) (σ : Fin R → Equiv.Perm (Fin 3))
    (sx sy : ∀ _j : Fin k, ∀ r : Fin R, Fin ((p r).length (m r)) → Fin 3 → Fin 5)
    (hsum : ∀ j r t i, (sx j r t i).val + (sy j r t i).val =
      (cwFourthBlockType (I r) (J r) (L r) i).val)
    (hprofile : ∀ j r a, (Finset.univ.filter
      (fun t : Fin ((p r).length (m r)) ↦ sx j r t 2 = a)).card = (p r).count a * m r)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r t,
        (sx (js (σ r 0)) r t 0).val + (sx (js (σ r 1)) r t 1).val +
          (sx (js (σ r 2)) r t 2).val = 4) →
      ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin k ↦ kronFin R (fun r ↦
        permObj (σ r) (regionTarget q ((p r).length (m r)) (sx j r) (sy j r)))))
      (kronFin R (fun r ↦ permObj (σ r) (regionSource (K := K) q (I r) (J r) (L r) (p r) (m r)))) := by
  classical
  let X := fun r ↦ permObj (σ r) (regionSource (K := K) q (I r) (J r) (L r) (p r) (m r))
  let Y := fun j r ↦ permObj (σ r) (regionTarget (K := K) q ((p r).length (m r)) (sx j r) (sy j r))
  let f := fun j r i ↦ regionMap (K := K) q (I r) (J r) (L r) (p r) (m r)
    (sx j r) (sy j r) ((σ r).symm i)
  let B := fun j ↦ kronFin R (Y j)
  let F := fun j ↦ kronFinFamilyModeMap R X (Y j) (f j)
  refine ⟨fun i ↦ ∑ j, (gradedBigAddSlot k B j i).comp (F j i), ?_⟩
  apply sum_slot_tensor
  · intro j
    apply kronFinFamilyModeMap_preserves_tensor
    intro r
    change PiTensorProduct.map (fun i ↦ regionMap q (I r) (J r) (L r) (p r) (m r)
      (sx j r) (sy j r) ((σ r).symm i))
      ((PiTensorProduct.reindex K _ (σ r)) (regionSource q (I r) (J r) (L r) (p r) (m r)).t) =
      (PiTensorProduct.reindex K _ (σ r)) (regionTarget q ((p r).length (m r)) (sx j r) (sy j r)).t
    rw [PiTensorProduct.map_reindex,
      regionMap_tensor q (I r) (J r) (L r) (p r) (m r) (sx j r) (sy j r)
        (hsum j r) (hprofile j r)]
  · intro js hnot
    have hbad : ∃ r t,
        (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sx (js (σ r i)) r t i) = 0 ∨
        (cwSquareCanonicalGrading K q).blockTensor (fun i ↦ sy (js (σ r i)) r t i) = 0 := by
      by_contra hn
      apply hnot
      apply hInduced js
      intro r t
      exact square_nonzero_sum_four q (fun i ↦ sx (js (σ r i)) r t i)
        (fun h ↦ hn ⟨r,t,Or.inl h⟩)
    obtain ⟨r,t,ht⟩ := hbad
    have hr := rotated_mixed_zero
      (regionSource (K := K) q (I r) (J r) (L r) (p r) (m r))
      (fun j ↦ regionTarget (K := K) q ((p r).length (m r)) (sx j r) (sy j r))
      (fun j ↦ regionMap (K := K) q (I r) (J r) (L r) (p r) (m r) (sx j r) (sy j r))
      (σ r) js (regionMap_mixed_zero q (I r) (J r) (L r) (p r) (m r)
        (fun j ↦ sx j r) (fun j ↦ sy j r) (fun j ↦ hsum j r)
        (fun j ↦ hprofile j r) (fun i ↦ js (σ r i)) t ht)
    exact family_mixed_zero X Y f js r hr

end MME.DWZC1SimultaneousChild

theorem solution
    {K : Type u} [Field K] (q R k : ℕ)
    (I J L : Fin R → Fin 9) (p : Fin R → IntegerZSplitProfile 5)
    (m : Fin R → ℕ) (σ : Fin R → Equiv.Perm (Fin 3))
    (sx sy : ∀ _j : Fin k, ∀ r : Fin R, Fin ((p r).length (m r)) → Fin 3 → Fin 5)
    (hsum : ∀ j r t i, (sx j r t i).val + (sy j r t i).val =
      (cwFourthBlockType (I r) (J r) (L r) i).val)
    (hprofile : ∀ j r a, (Finset.univ.filter
      (fun t : Fin ((p r).length (m r)) ↦ sx j r t 2 = a)).card = (p r).count a * m r)
    (hInduced : ∀ js : Fin 3 → Fin k,
      (∀ r t,
        (sx (js (σ r 0)) r t 0).val + (sx (js (σ r 1)) r t 1).val +
          (sx (js (σ r 2)) r t 2).val = 4) →
      ∃ j, js = fun _ ↦ j) :
    TensorObj.Restrict
      (bigAdd (fun j : Fin k ↦ kronFin R (fun r ↦
        permObj (σ r) (kronFin ((p r).length (m r)) (fun t ↦
          kron ((cwSquareCanonicalGrading K q).blockSubtensor (sx j r t))
            ((cwSquareCanonicalGrading K q).blockSubtensor (sy j r t)))))))
      (kronFin R (fun r ↦ permObj (σ r)
        (prescribedZPower (cwFourthConstituent K q (I r) (J r) (L r))
          (constituentBasis K q (I r) (J r) (L r) 2)
          (fun a : LiftedCoarseCoordinate.{u} q (L r) ↦ cwSquarePairGrade q a.down.val.1)
          (p r) (m r)))) := by
  exact MME.DWZC1SimultaneousChild.simultaneous_regional_restrict
    q R k I J L p m σ sx sy hsum hprofile hInduced
