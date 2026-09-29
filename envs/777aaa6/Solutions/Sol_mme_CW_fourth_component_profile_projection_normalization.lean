-- Prove2me | solution 1 for mme_CW_fourth_component_profile_projection_normalization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T09:18:52.571644+00:00
-- url     : https://prove2.me/submissions/a4b0b561-9da3-4a04-b481-9a0781df1ce5

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_complete_split_cw_fourth_label_certificate
import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Definitions.Def_mme_kronPow_position_permutation_linear_data
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
import Theorems.Thm_mme_kronFin_all_mode_projection_factorization
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj Module PiTensorProduct
open scoped Classical

universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZConstituentNormalization

theorem class_eq_span
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) :
    (T.basisAllAllowedGrading b P).classOf i 0 =
      Submodule.span K (b i '' {a | P i a}) := by
  classical
  simp [TensorObj.basisAllAllowedGrading, TensorObj.TypeGrading.classOf,
    cwBasisGrade]

theorem projection_yes
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (a : I i) (ha : P i a) :
    ((T.basisAllAllowedGrading b P).blockProj i 0 (b i a) : T.V i) = b i a := by
  have hm : b i a ∈ (T.basisAllAllowedGrading b P).classOf i 0 := by
    rw [class_eq_span]
    exact Submodule.subset_span ⟨a, ha, rfl⟩
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm]

theorem projection_no
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) (i : Fin 3) (a : I i) (ha : ¬ P i a) :
    (T.basisAllAllowedGrading b P).blockProj i 0 (b i a) = 0 := by
  classical
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _ 1 (by decide)
  apply Submodule.subset_span
  exact ⟨a, by simp [ha], rfl⟩

/-- The coordinate subspace has the literal selected vectors as its basis,
including when the selected index set is empty. -/
theorem exists_allowed_basis
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (P : ∀ i, I i → Prop) :
    ∃ β : ∀ i, Basis {a : I i // P i a} K
        ((T.basisAllAllowedGrading b P).classOf i 0),
      ∀ i a, (β i a : T.V i) = b i a.val := by
  classical
  have hB (i : Fin 3) : ∃ β : Basis {a : I i // P i a} K
      ((T.basisAllAllowedGrading b P).classOf i 0),
      ∀ a, (β a : T.V i) = b i a.val := by
    let v : {a : I i // P i a} → T.V i := fun a ↦ b i a.val
    have hi : LinearIndependent K v :=
      (b i).linearIndependent.comp _ Subtype.val_injective
    have hs : Submodule.span K (Set.range v) =
        (T.basisAllAllowedGrading b P).classOf i 0 := by
      rw [class_eq_span]
      congr 1
      ext x
      constructor
      · rintro ⟨a, rfl⟩
        exact ⟨a.val, a.property, rfl⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨⟨a, ha⟩, rfl⟩
    refine ⟨(Basis.span hi).map (LinearEquiv.ofEq _ _ hs), ?_⟩
    intro a
    simp only [Basis.map_apply, LinearEquiv.coe_ofEq_apply, Basis.span_apply]
    rfl
  exact ⟨fun i ↦ (hB i).choose, fun i ↦ (hB i).choose_spec⟩


open MME.DWZComponentRestriction MME.DWZRestrictedValue MME.StothersFourth
open MME.CompleteSplit.CWFourth

/-- A coordinate-surjective tensor map gives an actual equivalence after
both coarse coordinate selection and an arbitrary additional filter. -/
theorem filtered_tensor_equiv
    {K : Type u} [Field K] (T U : TensorObj K 3)
    {I J : Fin 3 → Type u}
    (b : ∀ i, Basis (I i) K (T.V i))
    (c : ∀ i, Basis (J i) K (U.V i))
    (P : ∀ i, I i → Prop)
    (e : ∀ i, {a : I i // P i a} ≃ J i)
    (f : ∀ i, T.V i →ₗ[K] U.V i)
    (hf : PiTensorProduct.map f T.t = U.t)
    (hyes : ∀ i a (ha : P i a), f i (b i a) = c i (e i ⟨a, ha⟩))
    (hno : ∀ i a, ¬ P i a → f i (b i a) = 0)
    (Q : ∀ i, J i → Prop) :
    let R := fun i a ↦ ∃ ha : P i a, Q i (e i ⟨a, ha⟩)
    let G := T.basisAllAllowedGrading b R
    let H := U.basisAllAllowedGrading c Q
    ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] H.classOf i 0,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (G.blockSubtensor (fun _ ↦ 0)).t =
          (H.blockSubtensor (fun _ ↦ 0)).t ∧
      ∀ i a (ha : P i a),
        F i (G.blockProj i 0 (b i a)) =
          H.blockProj i 0 (c i (e i ⟨a, ha⟩)) := by
  classical
  dsimp only
  let R := fun i a ↦ ∃ ha : P i a, Q i (e i ⟨a, ha⟩)
  let G := T.basisAllAllowedGrading b R
  let H := U.basisAllAllowedGrading c Q
  obtain ⟨β, hβ⟩ := exists_allowed_basis T b R
  obtain ⟨γ, hγ⟩ := exists_allowed_basis U c Q
  let E (i : Fin 3) : {a : I i // R i a} ≃ {a : J i // Q i a} :=
    { toFun := fun a ↦ ⟨e i ⟨a.val, a.property.choose⟩, a.property.choose_spec⟩
      invFun := fun a ↦ ⟨((e i).symm a.val).val,
        ⟨((e i).symm a.val).property, by simpa using a.property⟩⟩
      left_inv := by intro a; apply Subtype.ext; simp
      right_inv := by intro a; apply Subtype.ext; simp }
  let F (i : Fin 3) : G.classOf i 0 ≃ₗ[K] H.classOf i 0 :=
    (β i).equiv (γ i) (E i)
  have hproj (i : Fin 3) :
      (F i).toLinearMap.comp (G.blockProj i 0) =
        (H.blockProj i 0).comp (f i) := by
    apply (b i).ext
    intro a
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    by_cases ha : R i a
    · have hsource : G.blockProj i 0 (b i a) = β i ⟨a, ha⟩ := by
        apply Subtype.ext
        exact (projection_yes T b R i a ha).trans (hβ i ⟨a, ha⟩).symm
      rw [hsource]
      change (β i).equiv (γ i) (E i) (β i ⟨a, ha⟩) = _
      rw [(β i).equiv_apply]
      rw [hyes i a ha.choose]
      apply Subtype.ext
      exact (hγ i (E i ⟨a, ha⟩)).trans
        (projection_yes U c Q i (e i ⟨a, ha.choose⟩) ha.choose_spec).symm
    · rw [projection_no T b R i a ha, map_zero]
      by_cases hc : P i a
      · rw [hyes i a hc, projection_no U c Q i (e i ⟨a, hc⟩)
          (fun h ↦ ha ⟨hc, h⟩)]
      · rw [hno i a hc, map_zero]
  refine ⟨F, ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) T.t) =
        PiTensorProduct.map (fun i ↦ H.blockProj i 0) U.t
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp_rw [hproj]
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf]
  · intro i a ha
    have h := LinearMap.congr_fun (hproj i) (b i a)
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, hyes i a ha] using h

theorem word_basis_succ {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : Fin (n + 1) → I) :
    kronPowModeWordBasis T i b (n + 1) w =
      b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (Fin.tail w) := by
  letI : IsScalarTower K K (T.V i) := IsScalarTower.of_algebraMap_smul (by simp)
  exact (Basis.reindex_apply (b.tensorProduct (kronPowModeWordBasis T i b n))
    (Fin.consEquiv (fun _ : Fin (n+1) ↦ I)) w).trans
      (Basis.tensorProduct_apply b (kronPowModeWordBasis T i b n) (w 0) (Fin.tail w))

theorem recursive_basis_succ {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : PowIndex I (n + 1)) :
    kronPowModeBasis T i b (n + 1) w =
      b w.1 ⊗ₜ[K] kronPowModeBasis T i b n w.2 := by
  letI : IsScalarTower K K (T.V i) := IsScalarTower.of_algebraMap_smul (by simp)
  exact Basis.tensorProduct_apply b (kronPowModeBasis T i b n) w.1 w.2

theorem word_basis_eq_recursive
    {K : Type u} [Field K] (T : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (n : ℕ) (w : Fin n → I) :
    kronPowModeWordBasis T i b n w =
      kronPowModeBasis T i b n (PowIndex.ofFun n w) := by
  induction n with
  | zero =>
      exact (Basis.singleton_apply _ K w).trans
        (Basis.singleton_apply _ K _).symm
  | succ n ih =>
      rw [word_basis_succ, recursive_basis_succ]
      change b (w 0) ⊗ₜ[K] kronPowModeWordBasis T i b n (fun r ↦ w r.succ) =
        b (w 0) ⊗ₜ[K] kronPowModeBasis T i b n (PowIndex.ofFun n (fun r ↦ w r.succ))
      rw [ih]

theorem pow_map_tensor {K : Type u} [Field K] (T U : TensorObj K 3)
    (f : ∀ i, T.V i →ₗ[K] U.V i)
    (hf : PiTensorProduct.map f T.t = U.t) (n : ℕ) :
    PiTensorProduct.map (fun i ↦ kronPowModeMap i (f i) n) (T.kronPow n).t =
      (U.kronPow n).t := by
  induction n with
  | zero =>
      change PiTensorProduct.map (fun _ : Fin 3 ↦ LinearMap.id) _ = _
      rw [PiTensorProduct.map_id]
      rfl
  | succ n ih =>
      change PiTensorProduct.map
        (fun i ↦ TensorProduct.map (f i) (kronPowModeMap i (f i) n))
        (interchange T.t (T.kronPow n).t) = _
      rw [TensorObj.TypeGrading.kronMap_interchange, hf, ih]
      rfl

theorem pow_map_basis {K : Type u} [Field K] (T U : TensorObj K 3)
    (i : Fin 3) {I J : Type u}
    (b : Basis I K (T.V i)) (c : Basis J K (U.V i))
    (f : T.V i →ₗ[K] U.V i) (n : ℕ)
    (w : Fin n → I) (v : Fin n → J)
    (h : ∀ r, f (b (w r)) = c (v r)) :
    kronPowModeMap i f n (kronPowModeWordBasis T i b n w) =
      kronPowModeBasis U i c n (PowIndex.ofFun n v) := by
  rw [word_basis_eq_recursive]
  induction n with
  | zero =>
      change LinearMap.id (Basis.singleton _ K _) = Basis.singleton _ K _
      simp only [LinearMap.id_apply, Basis.singleton_apply]
  | succ n ih =>
      rw [recursive_basis_succ, recursive_basis_succ]
      change TensorProduct.map f (kronPowModeMap i f n)
        (b (w 0) ⊗ₜ[K] kronPowModeBasis T i b n
          (PowIndex.ofFun n (fun r ↦ w r.succ))) =
        c (v 0) ⊗ₜ[K] kronPowModeBasis U i c n
          (PowIndex.ofFun n (fun r ↦ v r.succ))
      rw [TensorProduct.map_tmul, h 0, ih (fun r ↦ w r.succ)
        (fun r ↦ v r.succ) (fun r ↦ h r.succ)]

theorem pow_map_zero {K : Type u} [Field K] (T U : TensorObj K 3)
    (i : Fin 3) {I : Type u} (b : Basis I K (T.V i))
    (f : T.V i →ₗ[K] U.V i) (n : ℕ) (w : Fin n → I)
    (h : ∃ r, f (b (w r)) = 0) :
    kronPowModeMap i f n (kronPowModeWordBasis T i b n w) = 0 := by
  rw [word_basis_eq_recursive]
  induction n with
  | zero => obtain ⟨r, _⟩ := h; exact r.elim0
  | succ n ih =>
      rw [recursive_basis_succ]
      change TensorProduct.map f (kronPowModeMap i f n)
        (b (w 0) ⊗ₜ[K] kronPowModeBasis T i b n
          (PowIndex.ofFun n (fun r ↦ w r.succ))) = 0
      rw [TensorProduct.map_tmul]
      obtain ⟨r, hr⟩ := h
      revert hr
      refine Fin.cases ?_ (fun r ↦ ?_) r
      · intro hr; rw [hr, TensorProduct.zero_tmul]
      · intro hr
        rw [ih (fun r ↦ w r.succ) ⟨r, hr⟩, TensorProduct.tmul_zero]

def coarseWordEquiv (q : ℕ) (s : Fin 9) (n : ℕ) :
    {w : Fin n → ULift.{u} (Coordinate q) //
      ∀ r, cwFourthPairGrade q (w r).down = s} ≃
        PowIndex (LiftedCoarseCoordinate.{u} q s) n where
  toFun w := PowIndex.ofFun n (fun r ↦ ⟨⟨(w.val r).down, w.property r⟩⟩)
  invFun w := ⟨fun r ↦ ⟨(PowIndex.get n w r).down.val⟩,
    fun r ↦ (PowIndex.get n w r).down.property⟩
  left_inv w := by
    apply Subtype.ext
    funext r
    simp only [PowIndex.get_ofFun]
  right_inv w := by
    apply (PowIndex.equivFun _ n).injective
    funext r
    change PowIndex.get n (PowIndex.ofFun n _) r = PowIndex.get n w r
    rw [PowIndex.get_ofFun]
    apply ULift.ext
    apply Subtype.ext
    rfl

theorem canonical_projection_yes
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9)
    (i : Fin 3) (a : ULift.{u} (Coordinate q))
    (ha : cwFourthPairGrade q a.down = cwFourthBlockType I J L i) :
    (cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i)
      (((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) a) =
        constituentBasis K q I J L i ⟨⟨a.down, ha⟩⟩ := by
  apply Subtype.ext
  rw [Basis.reindex_apply]
  have hm : cwFourthCanonicalBasis K q i a.down ∈
      (cwFourthCanonicalGrading K q).classOf i (cwFourthBlockType I J L i) := by
    apply Submodule.subset_span
    exact ⟨a.down, ha, rfl⟩
  change ((cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i)
    (cwFourthCanonicalBasis K q i a.down)).val = _
  rw [TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm]
  exact ((mme_complete_split_cw_fourth_label_certificate (K := K) q I J L).1
    i ⟨⟨a.down, ha⟩⟩).symm

theorem canonical_projection_no
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9)
    (i : Fin 3) (a : ULift.{u} (Coordinate q))
    (ha : cwFourthPairGrade q a.down ≠ cwFourthBlockType I J L i) :
    (cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i)
      (((cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm) a) = 0 := by
  rw [Basis.reindex_apply]
  apply TensorObj.TypeGrading.blockProj_apply_mem_ne _ _ _
    (cwFourthPairGrade q a.down) (Ne.symm ha)
  apply Submodule.subset_span
  exact ⟨a.down, rfl, rfl⟩

def zOnly {I : Fin 3 → Type u} (allowed : I 2 → Prop) (i : Fin 3) (a : I i) : Prop :=
  if h : i = 2 then allowed (h ▸ a) else True

theorem zOnly_grading_eq {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : I 2 → Prop) :
    T.basisAllAllowedGrading b (zOnly allowed) = T.basisZAllowedGrading (b 2) allowed := by
  classical
  have hc : (T.basisAllAllowedGrading b (zOnly allowed)).decomp =
      (T.basisZAllowedGrading (b 2) allowed).decomp := by
    funext i a
    by_cases hi : i = 2
    · subst i
      simp [TensorObj.basisAllAllowedGrading, TensorObj.basisZAllowedGrading, zOnly]
    · by_cases ha : a = 0
      · subst a
        simp [TensorObj.basisAllAllowedGrading, TensorObj.basisZAllowedGrading,
          zOnly, hi, cwBasisGrade, Basis.span_eq]
      · simp [TensorObj.basisAllAllowedGrading, TensorObj.basisZAllowedGrading,
          zOnly, hi, cwBasisGrade, Ne.symm ha]
  have extG (G H : T.TypeGrading 2) (h : G.decomp = H.decomp) : G = H := by
    cases G
    cases H
    cases h
    rfl
  exact extG _ _ hc

theorem constituent_power_filtered_equiv
    {K : Type u} [Field K] (q : ℕ) (I J L : Fin 9)
    (p : IntegerZSplitProfile 5) (m : ℕ) :
    let n := p.length m
    let T := cwFourthObj K q
    let C := cwFourthConstituent K q I J L
    let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
    let B := fun i ↦ kronPowModeWordBasis T i (b i) n
    let c := constituentBasis K q I J L
    let A := fun i ↦ kronPowModeBasis C i (c i) n
    let grade := fun a : LiftedCoarseCoordinate.{u} q L ↦
      cwSquarePairGrade q a.down.val.1
    let P := fun i (w : Fin n → ULift.{u} (Coordinate q)) ↦
      (∀ r, cwFourthPairGrade q (w r).down = cwFourthBlockType I J L i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter (fun r : Fin n ↦ cwSquarePairGrade q (w r).down.1 = a)).card =
          p.count a * m)
    let G := (T.kronPow n).basisAllAllowedGrading B P
    let H := (C.kronPow n).basisZAllowedGrading (A 2) (prescribedZWord grade p m)
    ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] H.classOf i 0,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (G.blockSubtensor (fun _ ↦ 0)).t =
          (prescribedZPower C (c 2) grade p m).t ∧
      ∀ i (w : Fin n → LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)),
        F i (G.blockProj i 0 (B i (fun r ↦ ⟨(w r).down.val⟩))) =
          H.blockProj i 0 (A i (PowIndex.ofFun n w)) := by
  classical
  dsimp only
  let n := p.length m
  let T := cwFourthObj K q
  let C := cwFourthConstituent K q I J L
  let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
  let B := fun i ↦ kronPowModeWordBasis T i (b i) n
  let c := constituentBasis K q I J L
  let A := fun i ↦ kronPowModeBasis C i (c i) n
  let grade := fun a : LiftedCoarseCoordinate.{u} q L ↦ cwSquarePairGrade q a.down.val.1
  let P0 := fun i (w : Fin n → ULift.{u} (Coordinate q)) ↦
    ∀ r, cwFourthPairGrade q (w r).down = cwFourthBlockType I J L i
  let e := fun i ↦ coarseWordEquiv q (cwFourthBlockType I J L i) n
  let f0 : ∀ i, T.V i →ₗ[K] C.V i :=
    fun i ↦ (cwFourthCanonicalGrading K q).blockProj i (cwFourthBlockType I J L i)
  let f := fun i ↦ kronPowModeMap (T := T) (S := C) i (f0 i) n
  have hf : PiTensorProduct.map f (T.kronPow n).t = (C.kronPow n).t :=
    pow_map_tensor T C f0 rfl n
  have hyes : ∀ i w (hw : P0 i w), f i (B i w) = A i (e i ⟨w, hw⟩) := by
    intro i w hw
    exact pow_map_basis T C i (b i) (c i) (f0 i) n w
      (fun r ↦ ⟨⟨(w r).down, hw r⟩⟩)
      (fun r ↦ canonical_projection_yes q I J L i (w r) (hw r))
  have hno : ∀ i w, ¬ P0 i w → f i (B i w) = 0 := by
    intro i w hw
    obtain ⟨r, hr⟩ := not_forall.mp hw
    exact pow_map_zero T C i (b i) (f0 i) n w
      ⟨r, canonical_projection_no q I J L i (w r) hr⟩
  let Q := zOnly (I := fun i ↦ PowIndex
    (LiftedCoarseCoordinate.{u} q (cwFourthBlockType I J L i)) n)
    (prescribedZWord grade p m)
  have h := filtered_tensor_equiv (T.kronPow n) (C.kronPow n) B A P0 e f hf hyes hno Q
  let R := fun i w ↦ ∃ hw : P0 i w, Q i (e i ⟨w, hw⟩)
  let P := fun i (w : Fin n → ULift.{u} (Coordinate q)) ↦
    P0 i w ∧ (i = 2 → ∀ a : Fin 5,
      (Finset.univ.filter (fun r : Fin n ↦ cwSquarePairGrade q (w r).down.1 = a)).card =
        p.count a * m)
  have hRP : R = P := by
    funext i w
    apply propext
    by_cases hi : i = 2
    · subst i
      have hcount (hw : P0 2 w) (a : Fin 5) :
          leftGradeCount grade (e 2 ⟨w, hw⟩) a =
            (Finset.univ.filter
              (fun r : Fin n ↦ cwSquarePairGrade q (w r).down.1 = a)).card := by
        let v : Fin n → LiftedCoarseCoordinate.{u} q L :=
          fun r ↦ ⟨⟨(w r).down, hw r⟩⟩
        have hv : PowIndex.get n (PowIndex.ofFun n v) = v := PowIndex.get_ofFun n v
        change (Finset.univ.filter
          (fun r : Fin n ↦ grade (PowIndex.get n (PowIndex.ofFun n v) r) = a)).card = _
        rw [hv]
      constructor
      · rintro ⟨hw, hq⟩
        change prescribedZWord grade p m (e 2 ⟨w, hw⟩) at hq
        exact ⟨hw, fun _ a ↦ (hcount hw a).symm.trans (hq a)⟩
      · rintro ⟨hw, hq⟩
        refine ⟨hw, ?_⟩
        change prescribedZWord grade p m (e 2 ⟨w, hw⟩)
        intro a
        exact (hcount hw a).trans (hq rfl a)
    · simp [R, P, Q, zOnly, hi]
  let result (G : (T.kronPow n).TypeGrading 2)
      (H : (C.kronPow n).TypeGrading 2) : Prop :=
    ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] H.classOf i 0,
      PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
        (G.blockSubtensor (fun _ ↦ 0)).t = (H.blockSubtensor (fun _ ↦ 0)).t ∧
      ∀ i a (ha : P0 i a), F i (G.blockProj i 0 (B i a)) =
        H.blockProj i 0 (A i (e i ⟨a, ha⟩))
  have hr : result ((T.kronPow n).basisAllAllowedGrading B R)
      ((C.kronPow n).basisAllAllowedGrading A Q) := h
  rw [hRP] at hr
  have hG := zOnly_grading_eq (C.kronPow n) A (prescribedZWord grade p m)
  change (C.kronPow n).basisAllAllowedGrading A Q = _ at hG
  rw [hG] at hr
  obtain ⟨F, hF, hB⟩ := hr
  refine ⟨F, hF, ?_⟩
  intro i w
  have hw : P0 i (fun r ↦ ULift.up (w r).down.val) := fun r ↦ (w r).down.property
  exact hB i (fun r ↦ ⟨(w r).down.val⟩) hw

set_option linter.unusedVariables false in
noncomputable def familyEquiv
    {K : Type u} [Field K] :
    ∀ (k : ℕ) (X Y : Fin k → TensorObj K 3)
      (E : ∀ r i, (X r).V i ≃ₗ[K] (Y r).V i) (i : Fin 3),
      (kronFin k X).V i ≃ₗ[K] (kronFin k Y).V i
  | 0, _, _, _, _ => LinearEquiv.refl K K
  | k+1, X, Y, E, i => TensorProduct.congr (E 0 i)
      (familyEquiv k (fun r ↦ X r.succ) (fun r ↦ Y r.succ)
        (fun r j ↦ E r.succ j) i)

theorem familyEquiv_map {K : Type u} [Field K] (k : ℕ)
    (X Y : Fin k → TensorObj K 3) (E : ∀ r i, (X r).V i ≃ₗ[K] (Y r).V i)
    (i : Fin 3) :
    (familyEquiv k X Y E i).toLinearMap =
      kronFinFamilyModeMap k X Y (fun r j ↦ (E r j).toLinearMap) i := by
  induction k with
  | zero => rfl
  | succ k ih =>
      change TensorProduct.map (E 0 i).toLinearMap
        (familyEquiv k _ _ _ i).toLinearMap =
          TensorProduct.map (E 0 i).toLinearMap
            (kronFinFamilyModeMap k _ _ _ i)
      rw [ih]

theorem exists_zOnly_basis {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (allowed : I 2 → Prop) :
    ∃ β : ∀ i, Basis {a : I i // zOnly allowed i a} K
        ((T.basisZAllowedGrading (b 2) allowed).classOf i 0),
      ∀ i a, (β i a : T.V i) = b i a.val := by
  have h := exists_allowed_basis T b (zOnly allowed)
  let result (G : T.TypeGrading 2) : Prop :=
    ∃ β : ∀ i, Basis {a : I i // zOnly allowed i a} K (G.classOf i 0),
      ∀ i a, (β i a : T.V i) = b i a.val
  have hr : result (T.basisAllAllowedGrading b (zOnly allowed)) := h
  rw [zOnly_grading_eq] at hr
  exact hr

theorem constituent_product_filtered_equiv
    {K : Type u} [Field K] {k : ℕ} (q : ℕ)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ) :
    let n := fun r ↦ (p r).length (m r)
    let T := cwFourthObj K q
    let C := fun r ↦ cwFourthConstituent K q (I r) (J r) (L r)
    let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
    let B := fun r i ↦ kronPowModeWordBasis T i (b i) (n r)
    let c := fun r ↦ constituentBasis K q (I r) (J r) (L r)
    let A := fun r i ↦ kronPowModeBasis (C r) i (c r i) (n r)
    let grade := fun r (a : LiftedCoarseCoordinate.{u} q (L r)) ↦
      cwSquarePairGrade q a.down.val.1
    let X := fun r ↦ T.kronPow (n r)
    let S := fun r ↦ prescribedZPower (C r) (c r 2) (grade r) (p r) (m r)
    let P := fun r i (w : Fin (n r) → ULift.{u} (Coordinate q)) ↦
      (∀ t, cwFourthPairGrade q (w t).down = cwFourthBlockType (I r) (J r) (L r) i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter
          (fun t : Fin (n r) ↦ cwSquarePairGrade q (w t).down.1 = a)).card =
            (p r).count a * m r)
    let Q := fun r ↦ zOnly
      (I := fun i ↦ PowIndex
        (LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i)) (n r))
      (prescribedZWord (grade r) (p r) (m r))
    let H := fun r ↦ ((C r).kronPow (n r)).basisZAllowedGrading
      (A r 2) (prescribedZWord (grade r) (p r) (m r))
    let BB := fun i ↦ kronFinModePiBasis k X i (fun r ↦ B r i)
    let G := (kronFin k X).basisAllAllowedGrading BB (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {w : PowIndex
          (LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i)) (n r) //
          Q r i w} K ((H r).classOf i 0),
      (∀ r i w, (β r i w : ((C r).kronPow (n r)).V i) = A r i w.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin k S).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin k S).t ∧
        ∀ i (w : ∀ r, Fin (n r) →
            LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i))
          (hw : ∀ r, Q r i (PowIndex.ofFun (n r) (w r))),
          F i (G.blockProj i 0 (BB i (fun r t ↦ ⟨(w r t).down.val⟩))) =
            kronFinModePiBasis k S i (fun r ↦ β r i)
              (fun r ↦ ⟨PowIndex.ofFun (n r) (w r), hw r⟩) := by
  classical
  dsimp only
  let n := fun r ↦ (p r).length (m r)
  let T := cwFourthObj K q
  let C := fun r ↦ cwFourthConstituent K q (I r) (J r) (L r)
  let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
  let B := fun r i ↦ kronPowModeWordBasis T i (b i) (n r)
  let c := fun r ↦ constituentBasis K q (I r) (J r) (L r)
  let A := fun r i ↦ kronPowModeBasis (C r) i (c r i) (n r)
  let grade := fun r (a : LiftedCoarseCoordinate.{u} q (L r)) ↦
    cwSquarePairGrade q a.down.val.1
  let X := fun r ↦ T.kronPow (n r)
  let S := fun r ↦ prescribedZPower (C r) (c r 2) (grade r) (p r) (m r)
  let P := fun r i (w : Fin (n r) → ULift.{u} (Coordinate q)) ↦
    (∀ t, cwFourthPairGrade q (w t).down = cwFourthBlockType (I r) (J r) (L r) i) ∧
    (i = 2 → ∀ a : Fin 5,
      (Finset.univ.filter
        (fun t : Fin (n r) ↦ cwSquarePairGrade q (w t).down.1 = a)).card =
          (p r).count a * m r)
  let Q := fun r ↦ zOnly
    (I := fun i ↦ PowIndex
      (LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i)) (n r))
    (prescribedZWord (grade r) (p r) (m r))
  let H := fun r ↦ ((C r).kronPow (n r)).basisZAllowedGrading
    (A r 2) (prescribedZWord (grade r) (p r) (m r))
  let BB := fun i ↦ kronFinModePiBasis k X i (fun r ↦ B r i)
  let G := (kronFin k X).basisAllAllowedGrading BB (fun i w ↦ ∀ r, P r i (w r))
  let Y := fun r ↦ (X r).basisAllAllowedSubtensor (B r) (P r)
  have hβ (r : Fin k) := exists_zOnly_basis ((C r).kronPow (n r)) (A r)
    (prescribedZWord (grade r) (p r) (m r))
  choose β hβ using hβ
  refine ⟨β, hβ, ?_⟩
  have hF (r : Fin k) := constituent_power_filtered_equiv (K := K)
    q (I r) (J r) (L r) (p r) (m r)
  choose E hE hEB using hF
  have hEtensor : ∀ r, PiTensorProduct.map (fun i ↦ (E r i).toLinearMap) (Y r).t =
      (S r).t := hE
  let EE := familyEquiv k Y S E
  have hEE : PiTensorProduct.map (fun i ↦ (EE i).toLinearMap)
      (kronFin k Y).t = (kronFin k S).t := by
    simp only [EE, familyEquiv_map]
    exact kronFinFamilyModeMap_preserves_tensor Y S
      (fun r i ↦ (E r i).toLinearMap) hEtensor
  obtain ⟨γ, hγ, F0, hF0, hF0B⟩ :=
    mme_kronFin_all_mode_projection_factorization X B P
  let F := fun i ↦ (F0 i).trans (EE i)
  refine ⟨F, ?_, ?_⟩
  · change PiTensorProduct.map
      (fun i ↦ (EE i).toLinearMap.comp (F0 i).toLinearMap) _ = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hF0, hEE]
  · intro i w hw
    let raw := fun r t ↦ (ULift.up (w r t).down.val : ULift.{u} (Coordinate q))
    have hraw : ∀ r, P r i (raw r) := by
      intro r
      refine ⟨fun t ↦ (w r t).down.property, ?_⟩
      intro hi
      subst i
      have hh := hw r
      change prescribedZWord (grade r) (p r) (m r)
        (PowIndex.ofFun (n r) (w r)) at hh
      intro a
      let v : Fin (n r) → LiftedCoarseCoordinate.{u} q (L r) := w r
      have he : PowIndex.get (n r) (PowIndex.ofFun (n r) v) = v :=
        PowIndex.get_ofFun (n r) v
      have hc := hh a
      change (Finset.univ.filter
        (fun t : Fin (n r) ↦ grade r
          (PowIndex.get (n r) (PowIndex.ofFun (n r) v) t) = a)).card = _ at hc
      rw [he] at hc
      exact hc
    change EE i (F0 i (G.blockProj i 0 (BB i raw))) = _
    rw [hF0B i raw hraw]
    change (EE i).toLinearMap
      (kronFinModePiBasis k Y i (fun r ↦ γ r i) (fun r ↦ ⟨raw r, hraw r⟩)) = _
    rw [familyEquiv_map]
    apply mme_kronFin_family_mode_map_selected_basis Y S i
      (fun r ↦ γ r i) (fun r ↦ β r i) (fun r j ↦ (E r j).toLinearMap)
      (fun r ↦ ⟨raw r, hraw r⟩) (fun r ↦ ⟨PowIndex.ofFun (n r) (w r), hw r⟩)
    intro r
    have hsrc : ((X r).basisAllAllowedGrading (B r) (P r)).blockProj i 0
        (B r i (raw r)) = γ r i ⟨raw r, hraw r⟩ := by
      apply Subtype.ext
      exact (projection_yes (X r) (B r) (P r) i (raw r) (hraw r)).trans
        (hγ r i ⟨raw r, hraw r⟩).symm
    change E r i (γ r i ⟨raw r, hraw r⟩) = _
    refine (congrArg (E r i) hsrc.symm).trans ?_
    refine (hEB r i (w r)).trans ?_
    apply Subtype.ext
    have hm : A r i (PowIndex.ofFun (n r) (w r)) ∈ (H r).classOf i 0 := by
      exact (hβ r i ⟨PowIndex.ofFun (n r) (w r), hw r⟩) ▸
        (β r i ⟨PowIndex.ofFun (n r) (w r), hw r⟩).property
    exact (congrArg (fun x : (H r).classOf i 0 ↦ (x : ((C r).kronPow (n r)).V i))
      (TensorObj.TypeGrading.blockProj_apply_mem _ _ _ _ hm)).trans
      (hβ r i ⟨PowIndex.ofFun (n r) (w r), hw r⟩).symm

end MME.DWZConstituentNormalization

open MME.DWZComponentRestriction MME.DWZRestrictedValue MME.StothersFourth
open MME.CompleteSplit.CWFourth

theorem solution
    {K : Type u} [Field K] {k : ℕ} (q : ℕ)
    (I J L : Fin k → Fin 9) (p : Fin k → IntegerZSplitProfile 5) (m : Fin k → ℕ) :
    let n := fun r ↦ (p r).length (m r)
    let T := cwFourthObj K q
    let C := fun r ↦ cwFourthConstituent K q (I r) (J r) (L r)
    let b := fun i ↦ (cwFourthCanonicalBasis K q i).reindex Equiv.ulift.symm
    let B := fun r i ↦ kronPowModeWordBasis T i (b i) (n r)
    let c := fun r ↦ constituentBasis K q (I r) (J r) (L r)
    let A := fun r i ↦ kronPowModeBasis (C r) i (c r i) (n r)
    let grade := fun r (a : LiftedCoarseCoordinate.{u} q (L r)) ↦
      cwSquarePairGrade q a.down.val.1
    let X := fun r ↦ T.kronPow (n r)
    let S := fun r ↦ prescribedZPower (C r) (c r 2) (grade r) (p r) (m r)
    let P := fun r i (w : Fin (n r) → ULift.{u} (Coordinate q)) ↦
      (∀ t, cwFourthPairGrade q (w t).down = cwFourthBlockType (I r) (J r) (L r) i) ∧
      (i = 2 → ∀ a : Fin 5,
        (Finset.univ.filter
          (fun t : Fin (n r) ↦ cwSquarePairGrade q (w t).down.1 = a)).card =
            (p r).count a * m r)
    let Q := fun r (i : Fin 3)
      (w : PowIndex (LiftedCoarseCoordinate.{u} q
        (cwFourthBlockType (I r) (J r) (L r) i)) (n r)) ↦
      if h : i = 2 then prescribedZWord (grade r) (p r) (m r)
        (Eq.ndrec (motive := fun j : Fin 3 ↦ PowIndex (LiftedCoarseCoordinate.{u} q
          (cwFourthBlockType (I r) (J r) (L r) j)) (n r)) w h) else True
    let H := fun r ↦ ((C r).kronPow (n r)).basisZAllowedGrading
      (A r 2) (prescribedZWord (grade r) (p r) (m r))
    let BB := fun i ↦ kronFinModePiBasis k X i (fun r ↦ B r i)
    let G := (kronFin k X).basisAllAllowedGrading BB (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {w : PowIndex
          (LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i)) (n r) //
          Q r i w} K ((H r).classOf i 0),
      (∀ r i w, (β r i w : ((C r).kronPow (n r)).V i) = A r i w.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin k S).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin k S).t ∧
        ∀ i (w : ∀ r, Fin (n r) →
            LiftedCoarseCoordinate.{u} q (cwFourthBlockType (I r) (J r) (L r) i))
          (hw : ∀ r, Q r i (PowIndex.ofFun (n r) (w r))),
          F i (G.blockProj i 0 (BB i (fun r t ↦ ⟨(w r t).down.val⟩))) =
            kronFinModePiBasis k S i (fun r ↦ β r i)
              (fun r ↦ ⟨PowIndex.ofFun (n r) (w r), hw r⟩) := by
  exact MME.DWZConstituentNormalization.constituent_product_filtered_equiv q I J L p m
