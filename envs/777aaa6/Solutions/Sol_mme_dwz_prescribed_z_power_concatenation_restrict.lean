-- Prove2me | solution 1 for mme_dwz_prescribed_z_power_concatenation_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-07T06:34:08.135148+00:00
-- url     : https://prove2.me/submissions/6f6d39e5-074a-486f-8978-55c28733a09a

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Theorems.Thm_mme_restrict_basisZAllowedSubtensor_of_vanishes

open MME MME.DWZComponentRestriction MME.DWZRestrictedValue Module
open PiTensorProduct TensorProduct BigOperators

universe u

set_option autoImplicit false
set_option warningAsError true

private theorem interchange_pure
    {K : Type u} [Field K] {V W : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    (v : ∀ i, V i) (w : ∀ i, W i) :
    interchange (tprod K v) (tprod K w) =
      tprod K (fun i ↦ v i ⊗ₜ[K] w i) := by
  unfold interchange
  rw [PiTensorProduct.lift.tprod]
  change (PiTensorProduct.lift (interchangeInner v)) (tprod K w) = _
  rw [PiTensorProduct.lift.tprod]
  rfl

private theorem map_interchange
    {K : Type u} [Field K] {V₁ V₂ V₃ V₄ : Fin 3 → Type u}
    [∀ i, AddCommGroup (V₁ i)] [∀ i, Module K (V₁ i)]
    [∀ i, AddCommGroup (V₂ i)] [∀ i, Module K (V₂ i)]
    [∀ i, AddCommGroup (V₃ i)] [∀ i, Module K (V₃ i)]
    [∀ i, AddCommGroup (V₄ i)] [∀ i, Module K (V₄ i)]
    (f : ∀ i, V₁ i →ₗ[K] V₃ i) (g : ∀ i, V₂ i →ₗ[K] V₄ i)
    (a : PiTensorProduct K V₁) (b : PiTensorProduct K V₂) :
    PiTensorProduct.map (fun i ↦ TensorProduct.map (f i) (g i)) (interchange a b) =
      interchange (PiTensorProduct.map f a) (PiTensorProduct.map g b) := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod c' w =>
      simp only [map_smul, LinearMap.smul_apply]
      rw [interchange_pure, PiTensorProduct.map_tprod, PiTensorProduct.map_tprod,
        PiTensorProduct.map_tprod, interchange_pure]
      simp only [TensorProduct.map_tmul]
    | add x y ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
  | add x y ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

private theorem map_assoc_symm
    {K : Type u} [Field K] {V W U : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    [∀ i, AddCommGroup (W i)] [∀ i, Module K (W i)]
    [∀ i, AddCommGroup (U i)] [∀ i, Module K (U i)]
    (a : PiTensorProduct K V) (b : PiTensorProduct K W) (c : PiTensorProduct K U) :
    PiTensorProduct.map
      (fun i ↦ (TensorProduct.assoc K (V i) (W i) (U i)).symm.toLinearMap)
      (interchange a (interchange b c)) = interchange (interchange a b) c := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod ca v =>
    induction b using PiTensorProduct.induction_on with
    | smul_tprod cb w =>
      induction c using PiTensorProduct.induction_on with
      | smul_tprod cc x =>
        simp only [map_smul, LinearMap.smul_apply, smul_smul]
        rw [interchange_pure, interchange_pure, PiTensorProduct.map_tprod,
          interchange_pure, interchange_pure]
        simp only [LinearEquiv.coe_coe, TensorProduct.assoc_symm_tmul]
        congr 1
        ring
      | add x y ih₁ ih₂ => simp only [map_add, ih₁, ih₂]
    | add x y ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]
  | add x y ih₁ ih₂ => simp only [map_add, LinearMap.add_apply, ih₁, ih₂]

private theorem map_lid_symm
    {K : Type u} [Field K] {V : Fin 3 → Type u}
    [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]
    (a : PiTensorProduct K V) :
    PiTensorProduct.map (fun i ↦ (TensorProduct.lid K (V i)).symm.toLinearMap) a =
      interchange (tprod K (fun _ ↦ (1 : K))) a := by
  induction a using PiTensorProduct.induction_on with
  | smul_tprod c v =>
    simp only [map_smul]
    rw [PiTensorProduct.map_tprod, interchange_pure]
    rfl
  | add x y ih₁ ih₂ => simp only [map_add, ih₁, ih₂]

private theorem grade_count_succ
    {ι : Type u} {t n : ℕ} (grade : ι → Fin t)
    (x : ι) (w : PowIndex ι n) (a : Fin t) :
    leftGradeCount (n := n + 1) grade (x, w) a =
      (if grade x = a then 1 else 0) + leftGradeCount grade w a := by
  classical
  simp only [leftGradeCount, Finset.card_filter, Fin.sum_univ_succ]
  rfl

private theorem split_power_with_counts
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t) (m n : ℕ) :
    ∃ f : ∀ i, (T.kronPow (m + n)).V i →ₗ[K]
        ((T.kronPow m).V i ⊗[K] (T.kronPow n).V i),
      PiTensorProduct.map f (T.kronPow (m + n)).t =
        interchange (T.kronPow m).t (T.kronPow n).t ∧
      ∀ w : PowIndex ι (m + n),
        ∃ x : PowIndex ι m, ∃ y : PowIndex ι n,
          (∀ a, leftGradeCount grade w a =
            leftGradeCount grade x a + leftGradeCount grade y a) ∧
          f 2 (kronPowModeBasis T 2 bZ (m + n) w) =
            kronPowModeBasis T 2 bZ m x ⊗ₜ[K] kronPowModeBasis T 2 bZ n y := by
  classical
  induction m with
  | zero =>
    rw [Nat.zero_add]
    refine ⟨fun i ↦ (TensorProduct.lid K ((T.kronPow n).V i)).symm.toLinearMap,
      map_lid_symm (T.kronPow n).t, ?_⟩
    intro w
    refine ⟨PUnit.unit, w, ?_, ?_⟩
    · intro a
      simp [leftGradeCount]
    · change (TensorProduct.lid K ((T.kronPow n).V 2)).symm
        (kronPowModeBasis T 2 bZ n w) =
        (Basis.singleton (PowIndex ι 0) K) PUnit.unit ⊗ₜ[K]
          kronPowModeBasis T 2 bZ n w
      rw [Basis.singleton_apply, TensorProduct.lid_symm_apply]
  | succ m ih =>
    obtain ⟨f, hf, hw⟩ := ih
    rw [Nat.succ_add]
    let g := fun i ↦
      (TensorProduct.assoc K (T.V i) ((T.kronPow m).V i)
        ((T.kronPow n).V i)).symm.toLinearMap.comp
        (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i) (f i))
    refine ⟨g, ?_, ?_⟩
    · change PiTensorProduct.map
        (fun i ↦ (TensorProduct.assoc K (T.V i) ((T.kronPow m).V i)
          ((T.kronPow n).V i)).symm.toLinearMap.comp
          (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i) (f i)))
        (interchange T.t (T.kronPow (m + n)).t) = _
      rw [PiTensorProduct.map_comp, LinearMap.comp_apply, map_interchange,
        PiTensorProduct.map_id, LinearMap.id_apply, hf]
      exact map_assoc_symm T.t (T.kronPow m).t (T.kronPow n).t
    · rintro ⟨z, w⟩
      obtain ⟨x, y, hcount, hb⟩ := hw w
      refine ⟨(z, x), y, ?_, ?_⟩
      · intro a
        rw [grade_count_succ, grade_count_succ, hcount]
        exact (Nat.add_assoc _ _ _).symm
      · simp only [kronPowModeBasis]
        change (TensorProduct.assoc K (T.V 2) ((T.kronPow m).V 2)
          ((T.kronPow n).V 2)).symm
          (TensorProduct.map (LinearMap.id : T.V 2 →ₗ[K] T.V 2) (f 2)
            ((Basis.tensorProduct bZ (kronPowModeBasis T 2 bZ (m + n))) (z, w))) =
          ((Basis.tensorProduct bZ (kronPowModeBasis T 2 bZ m)) (z, x)) ⊗ₜ[K]
            kronPowModeBasis T 2 bZ n y
        rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply,
          TensorProduct.map_tmul, LinearMap.id_apply, hb,
          TensorProduct.assoc_symm_tmul]

private theorem disallowed_Z_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u}
    (bZ : Basis ι K (T.V 2)) (allowed : ι → Prop) [DecidablePred allowed]
    (j : ι) (hj : ¬ allowed j) :
    (T.basisZAllowedGrading bZ allowed).blockProj 2 0 (bZ j) = 0 := by
  classical
  let G := T.basisZAllowedGrading bZ allowed
  have hx : bZ j ∈ G.classOf 2 1 := by
    change bZ j ∈ cwBasisGrade bZ
      (fun k ↦ if allowed k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal 2).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Type u} {t : ℕ}
    (bZ : Basis ι K (T.V 2)) (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m n : ℕ) :
    TensorObj.Restrict
      (TensorObj.kron (prescribedZPower T bZ grade p m)
        (prescribedZPower T bZ grade p n))
      (prescribedZPower T bZ grade p (m + n)) := by
  classical
  have hlength : p.length (m + n) = p.length m + p.length n := Nat.mul_add _ _ _
  unfold prescribedZPower prescribedZWord
  rw [hlength]
  let M := T.kronPow (p.length m)
  let N := T.kronPow (p.length n)
  let bM := kronPowModeBasis T 2 bZ (p.length m)
  let bN := kronPowModeBasis T 2 bZ (p.length n)
  let GM := M.basisZAllowedGrading bM (prescribedZWord grade p m)
  let GN := N.basisZAllowedGrading bN (prescribedZWord grade p n)
  obtain ⟨f, hf, hw⟩ := split_power_with_counts T bZ grade (p.length m) (p.length n)
  let maps := fun i ↦ (TensorProduct.map (GM.blockProj i 0)
    (GN.blockProj i 0)).comp (f i)
  refine @mme_restrict_basisZAllowedSubtensor_of_vanishes K _
    (T.kronPow (p.length m + p.length n))
    (TensorObj.kron (M.basisZAllowedSubtensor bM (prescribedZWord grade p m))
      (N.basisZAllowedSubtensor bN (prescribedZWord grade p n)))
    (PowIndex ι (p.length m + p.length n))
    (kronPowModeBasis T 2 bZ (p.length m + p.length n))
    (fun w ↦ ∀ a, leftGradeCount grade w a = p.count a * (m + n))
    (fun _ ↦ Classical.propDecidable _) maps ?_ ?_
  · change PiTensorProduct.map
      (fun i ↦ (TensorProduct.map (GM.blockProj i 0) (GN.blockProj i 0)).comp (f i))
      (T.kronPow (p.length m + p.length n)).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf, map_interchange]
    rfl
  · intro w hnot
    obtain ⟨x, y, hcount, hb⟩ := hw w
    have hbad : ¬ prescribedZWord grade p m x ∨ ¬ prescribedZWord grade p n y := by
      by_contra h
      push_neg at h
      apply hnot
      intro a
      rw [hcount, h.1 a, h.2 a]
      exact (Nat.mul_add _ _ _).symm
    change TensorProduct.map (GM.blockProj 2 0) (GN.blockProj 2 0)
      (f 2 (kronPowModeBasis T 2 bZ (p.length m + p.length n) w)) = 0
    rw [hb, TensorProduct.map_tmul]
    rcases hbad with hx | hy
    · rw [disallowed_Z_projection_zero M bM _ x hx, zero_tmul]
    · rw [disallowed_Z_projection_zero N bN _ y hy, tmul_zero]
