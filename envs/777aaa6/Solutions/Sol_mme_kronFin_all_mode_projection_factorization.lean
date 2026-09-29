-- Prove2me | solution 1 for mme_kronFin_all_mode_projection_factorization
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:27:52.535187+00:00
-- url     : https://prove2.me/submissions/633ba1c0-8d4d-433d-9be5-7e61ba989c6c

import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Definitions.Def_mme_complete_split_profile_projection
import Theorems.Thm_mme_kronFin_family_mode_map_selected_basis
import Mathlib.Algebra.Module.Submodule.Equiv
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj Module PiTensorProduct

universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

namespace MME.DWZProductProjection

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

/-- Projection onto factorwise allowed product-basis words is linearly
equivalent, with exact basis action, to the product of the projected factors. -/
theorem product_projection_factorization
    {K : Type u} [Field K] {n : ℕ}
    (X : Fin n → TensorObj K 3)
    {I : Fin n → Fin 3 → Type u}
    (b : ∀ r i, Basis (I r i) K ((X r).V i))
    (P : ∀ r i, I r i → Prop) :
    let Y := fun r ↦ (X r).basisAllAllowedSubtensor (b r) (P r)
    let B := fun i ↦ kronFinModePiBasis n X i (fun r ↦ b r i)
    let G := (kronFin n X).basisAllAllowedGrading B (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {a : I r i // P r i a} K
        (((X r).basisAllAllowedGrading (b r) (P r)).classOf i 0),
      (∀ r i a, (β r i a : (X r).V i) = b r i a.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin n Y).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin n Y).t ∧
        ∀ i (w : ∀ r, I r i) (hw : ∀ r, P r i (w r)),
          F i (G.blockProj i 0 (B i w)) =
            kronFinModePiBasis n Y i (fun r ↦ β r i)
              (fun r ↦ ⟨w r, hw r⟩) := by
  classical
  dsimp only
  let Y := fun r ↦ (X r).basisAllAllowedSubtensor (b r) (P r)
  let B := fun i ↦ kronFinModePiBasis n X i (fun r ↦ b r i)
  let G := (kronFin n X).basisAllAllowedGrading B (fun i w ↦ ∀ r, P r i (w r))
  have hB (r : Fin n) := exists_allowed_basis (X r) (b r) (P r)
  let β := fun r ↦ (hB r).choose
  have hβ : ∀ r i a, (β r i a : (X r).V i) = b r i a.val :=
    fun r ↦ (hB r).choose_spec
  refine ⟨β, hβ, ?_⟩
  obtain ⟨γ, hγ⟩ := exists_allowed_basis (kronFin n X) B
    (fun i w ↦ ∀ r, P r i (w r))
  let C := fun i ↦ kronFinModePiBasis n Y i (fun r ↦ β r i)
  let e (i : Fin 3) : {w : ∀ r, I r i // ∀ r, P r i (w r)} ≃
      (∀ r, {a : I r i // P r i a}) := Equiv.subtypePiEquivPi
  let F (i : Fin 3) : G.classOf i 0 ≃ₗ[K] (kronFin n Y).V i :=
    (γ i).equiv (C i) (e i)
  let proj := fun r i ↦ ((X r).basisAllAllowedGrading (b r) (P r)).blockProj i 0
  let map := kronFinFamilyModeMap n X Y proj
  have hlocal (r : Fin n) (i : Fin 3) (a : I r i) (ha : P r i a) :
      proj r i (b r i a) = β r i ⟨a, ha⟩ := by
    apply Subtype.ext
    exact (projection_yes (X r) (b r) (P r) i a ha).trans (hβ r i ⟨a, ha⟩).symm
  have hglobal (i : Fin 3) (w : ∀ r, I r i) (hw : ∀ r, P r i (w r)) :
      G.blockProj i 0 (B i w) = γ i ⟨w, hw⟩ := by
    apply Subtype.ext
    exact (projection_yes (kronFin n X) B (fun i w ↦ ∀ r, P r i (w r))
      i w hw).trans (hγ i ⟨w, hw⟩).symm
  have hselected (i : Fin 3) (w : ∀ r, I r i) (hw : ∀ r, P r i (w r)) :
      map i (B i w) = C i (fun r ↦ ⟨w r, hw r⟩) := by
    exact mme_kronFin_family_mode_map_selected_basis X Y i
      (fun r ↦ b r i) (fun r ↦ β r i) proj w (fun r ↦ ⟨w r, hw r⟩)
      (fun r ↦ hlocal r i (w r) (hw r))
  have hcomm (i : Fin 3) : (F i).toLinearMap.comp (G.blockProj i 0) = map i := by
    apply (B i).ext
    intro w
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    by_cases hw : ∀ r, P r i (w r)
    · rw [hglobal i w hw]
      exact ((γ i).equiv_apply ⟨w, hw⟩ (C i) (e i)).trans (hselected i w hw).symm
    · rw [projection_no (kronFin n X) B (fun i w ↦ ∀ r, P r i (w r)) i w hw,
        map_zero]
      symm
      apply kronFinFamilyModeMap_basis_eq_zero_of_exists X Y i (fun r ↦ b r i) proj w
      obtain ⟨r, hr⟩ := not_forall.mp hw
      exact ⟨r, projection_no (X r) (b r) (P r) i (w r) hr⟩
  refine ⟨F, ?_, ?_⟩
  · change PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
      (PiTensorProduct.map (fun i ↦ G.blockProj i 0) (kronFin n X).t) = _
    rw [← LinearMap.comp_apply, ← PiTensorProduct.map_comp]
    simp_rw [hcomm]
    exact kronFinFamilyModeMap_preserves_tensor X Y proj (fun _ ↦ rfl)
  · intro i w hw
    rw [hglobal i w hw]
    exact (γ i).equiv_apply ⟨w, hw⟩ (C i) (e i)

end MME.DWZProductProjection

theorem solution
    {K : Type u} [Field K] {n : ℕ}
    (X : Fin n → TensorObj K 3)
    {I : Fin n → Fin 3 → Type u}
    (b : ∀ r i, Basis (I r i) K ((X r).V i))
    (P : ∀ r i, I r i → Prop) :
    let Y := fun r ↦ (X r).basisAllAllowedSubtensor (b r) (P r)
    let B := fun i ↦ kronFinModePiBasis n X i (fun r ↦ b r i)
    let G := (kronFin n X).basisAllAllowedGrading B (fun i w ↦ ∀ r, P r i (w r))
    ∃ β : ∀ r i, Basis {a : I r i // P r i a} K
        (((X r).basisAllAllowedGrading (b r) (P r)).classOf i 0),
      (∀ r i a, (β r i a : (X r).V i) = b r i a.val) ∧
      ∃ F : ∀ i, G.classOf i 0 ≃ₗ[K] (kronFin n Y).V i,
        PiTensorProduct.map (fun i ↦ (F i).toLinearMap)
          (G.blockSubtensor (fun _ ↦ 0)).t = (kronFin n Y).t ∧
        ∀ i (w : ∀ r, I r i) (hw : ∀ r, P r i (w r)),
          F i (G.blockProj i 0 (B i w)) =
            kronFinModePiBasis n Y i (fun r ↦ β r i)
              (fun r ↦ ⟨w r, hw r⟩) := by
  exact MME.DWZProductProjection.product_projection_factorization X b P

