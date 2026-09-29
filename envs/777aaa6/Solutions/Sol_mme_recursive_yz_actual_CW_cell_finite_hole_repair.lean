-- Prove2me | solution 1 for mme_recursive_yz_actual_CW_cell_finite_hole_repair
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-12T11:07:34.571085+00:00
-- url     : https://prove2.me/submissions/6b371283-6073-44fa-9fe7-835987f8ab27

import Definitions.Def_mme_recursive_yz_CW_cells
import Theorems.Thm_mme_recursive_yz_cell_uniform_shuffle
import Theorems.Thm_mme_modern_three_mode_finite_hole_repair
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Definitions.Def_mme_TypeGrading_kron
import Definitions.Def_mme_strassen_preorder
import Mathlib.LinearAlgebra.Basis.Submodule

open BigOperators MME MME.TensorObj MME.CompleteSplit MME.DWZStep1Support
  MME.DWZComponentRestriction MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.DWZSquare MME.ModernRepair Module
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000
universe u v w

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

private theorem cell_uniform_instances {P C W D : Type*} [Fintype P] [Fintype W]
    (cell : P → C) (grade : W → D) (shape : C → D) (mu : C → W → ℕ)
    (fB : Fintype (CellWord cell grade shape mu)) (dB : DecidableEq (CellWord cell grade shape mu))
    (fE : Fintype (cellPerm cell)) (dE : DecidableEq (cellPerm cell)) :
    ∃ system : @AvailableBlockShuffle (CellWord cell grade shape mu) (cellPerm cell) fB dB fE dE,
      ∀ e x, (@AvailableBlockShuffle.move _ _ fB dB fE dE system e x).val =
        fun p ↦ x.val (e.val.symm p) := by
  classical
  let fB0 : Fintype (CellWord cell grade shape mu) :=
    @Subtype.fintype (P → W) _ (fun _ ↦ inferInstance) inferInstance
  let dB0 : DecidableEq (CellWord cell grade shape mu) := fun a b ↦ Subtype.instDecidableEq a b
  let fE0 : Fintype (cellPerm cell) :=
    @Subtype.fintype (Equiv.Perm P) (Membership.mem (cellPerm cell)) (fun _ ↦ inferInstance) inferInstance
  let dE0 : DecidableEq (cellPerm cell) := fun a b ↦ Subtype.instDecidableEq a b
  rw [show fB = fB0 from Subsingleton.elim _ _, show dB = dB0 from Subsingleton.elim _ _,
    show fE = fE0 from Subsingleton.elim _ _, show dE = dE0 from Subsingleton.elim _ _]
  exact mme_recursive_yz_cell_uniform_shuffle cell grade shape mu


private theorem label_reindex {P : Type v} (q ell L : ℕ) (positions : Fin L ≃ P)
    (sigma : Equiv.Perm P) (x : WordIndex.{u} q ell L) :
    CWCells.label q ell L positions (fun r ↦ x (leafPermutation ell L positions sigma r)) =
      fun p ↦ CWCells.label q ell L positions x (sigma p) := by
  funext p r
  simp [CWCells.label, leafPermutation]

private theorem literal_restrict_projected_univ
    {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} {Label : Fin 3 → Type v}
    [∀ i, Fintype (Label i)] [∀ i, DecidableEq (Label i)]
    (b : ∀ i, Basis (I i) K (T.V i)) (label : ∀ i, I i → Label i) :
    Restrict T (projected T b label (fun _ ↦ Finset.univ)) := by
  have hproj : (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) =
      fun i ↦ (LinearMap.id : T.V i →ₗ[K] T.V i) := by
    funext i
    apply (b i).ext
    intro x
    simp [basisLabelProjection, Basis.constr_basis]
  refine ⟨fun _ ↦ LinearMap.id, ?_⟩
  change PiTensorProduct.map (fun _ ↦ LinearMap.id)
    (PiTensorProduct.map (fun i ↦ basisLabelProjection (b i) (label i) Finset.univ) T.t) = T.t
  rw [hproj]
  simp only [PiTensorProduct.map_id, LinearMap.id_apply]

theorem solution {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P)
    (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    let S := unbroken K q ell L positions cell shape mu
    let G := grading K q ell L positions cell shape mu
    ∃ B : ∀ i, Basis (Coord.{u} q ell L positions cell shape mu i) K (S.V i),
    ∃ blockLabel : ∀ i, Coord.{u} q ell L positions cell shape mu i → Block ell cell shape mu i,
      (∀ i x, (G.classOf i 0).subtype (B i x) = basis K q ell L i x.val) ∧
      (∀ i x, (blockLabel i x).val = CWCells.label q ell L positions x.val) ∧
      ∀ d h : ℕ,
        (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) < d ^ h →
        ∀ holes : Fin (8 ^ h) → (i : Fin 3) → Finset (Block ell cell shape mu i),
          (∀ j i, 4 * d * (holes j i).card ≤ Nat.card (Block ell cell shape mu i)) →
          Restrict S (bigAdd (fun j ↦ projected S B blockLabel (fun i ↦ Finset.univ \ holes j i))) := by
  classical
  let S := unbroken K q ell L positions cell shape mu
  let G := grading K q ell L positions cell shape mu
  have hbases (i : Fin 3) : ∃ B : Basis (Coord.{u} q ell L positions cell shape mu i) K (S.V i),
      ∀ x, (G.classOf i 0).subtype (B x) = basis K q ell L i x.val :=
    allowed_basis_exists (source K q ell L) (basis K q ell L)
      (allowed q ell L positions cell shape mu) i
  choose B hB using hbases
  let blockLabel : ∀ i, Coord.{u} q ell L positions cell shape mu i → Block ell cell shape mu i :=
    fun _ x ↦ ⟨CWCells.label q ell L positions x.val, x.property⟩
  have hsystems (i : Fin 3) : ∃ system : AvailableBlockShuffle
      (Block ell cell shape mu i) (cellPerm cell),
      ∀ e x, (system.move e x).val = fun p ↦ x.val (e.val.symm p) :=
    cell_uniform_instances cell grade (fun c ↦ shape c i) (mu i)
      inferInstance inferInstance inferInstance inferInstance
  choose system hsystem using hsystems
  have hallowed (e : cellPerm cell) (i : Fin 3) (x : WordIndex.{u} q ell L) :
      allowed q ell L positions cell shape mu i
          (fun r ↦ x (leafPermutation ell L positions e.val.symm r)) ↔
        allowed q ell L positions cell shape mu i x := by
    have forward (e : cellPerm cell) (f : P → CompleteWord ell)
        (hf : (∀ p, grade (f p) = shape (cell p) i) ∧ Useful cell (mu i) f) :
        (∀ p, grade (f (e.val.symm p)) = shape (cell p) i) ∧
          Useful cell (mu i) (fun p ↦ f (e.val.symm p)) := by
      have H := ((system i).move e ⟨f, hf⟩).property
      rw [hsystem] at H
      exact H
    unfold allowed
    rw [label_reindex]
    constructor
    · intro H
      have H' := forward e⁻¹ _ H
      simpa only [Subgroup.coe_inv, Equiv.Perm.inv_def, Equiv.symm_symm, Equiv.symm_apply_apply] using H'
    · exact forward e _
  have hactions (e : cellPerm cell) :
      ∃ Ψ : ∀ i, S.V i ≃ₗ[K] S.V i,
      ∃ basisImage : ∀ i, Coord.{u} q ell L positions cell shape mu i →
          Coord.{u} q ell L positions cell shape mu i,
        PiTensorProduct.map (fun i ↦ (Ψ i).toLinearMap) S.t = S.t ∧
        (∀ i x, Ψ i (B i x) = B i (basisImage i x)) ∧
        (∀ i x, blockLabel i (basisImage i x) = (system i).move e (blockLabel i x)) := by
    let perm := leafPermutation ell L positions e.val.symm
    obtain ⟨A, hA, hAt⟩ := mme_kronPow_position_permutation_linear_equiv (CWObj K q)
      (fun i ↦ (cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
      (L * 2 ^ (ell - 1)) perm
    obtain ⟨Ψ, ht, hinc⟩ := allowed_automorphism (source K q ell L) (basis K q ell L)
      (allowed q ell L positions cell shape mu) A
      (fun _ ↦ kronPowWordReindex perm (ULift.{u} (Fin (q + 2)))) hA
      (hallowed e) hAt
    let basisImage : ∀ i, Coord.{u} q ell L positions cell shape mu i →
        Coord.{u} q ell L positions cell shape mu i :=
      fun i x ↦ ⟨fun r ↦ x.val (perm r), (hallowed e i x.val).2 x.property⟩
    refine ⟨Ψ, basisImage, ht, ?_, ?_⟩
    · intro i x
      apply Subtype.val_injective
      have hi := LinearMap.congr_fun (hinc i) (B i x)
      simp only [LinearMap.comp_apply] at hi
      change (G.classOf i 0).subtype (Ψ i (B i x)) =
        (G.classOf i 0).subtype (B i (basisImage i x))
      change (G.classOf i 0).subtype (Ψ i (B i x)) =
        A i ((G.classOf i 0).subtype (B i x)) at hi
      exact hi.trans ((congrArg (A i) (hB i x)).trans
        ((hA i x.val).trans (hB i (basisImage i x)).symm))
    · intro i x
      apply Subtype.ext
      change CWCells.label q ell L positions (fun r ↦ x.val (perm r)) = _
      rw [label_reindex, hsystem]
  choose Ψ basisImage ht hb hl using hactions
  refine ⟨B, blockLabel, hB, fun _ _ ↦ rfl, ?_⟩
  intro d h hcapacity holes hholes
  have H := mme_modern_three_mode_finite_hole_repair S B blockLabel system
    (fun e i ↦ (Ψ e i).toLinearMap) basisImage hb hl ht d h
    (fun _ ↦ Finset.univ) holes
    (by simpa only [Nat.card_eq_fintype_card] using hholes)
    (by simpa only [Finset.card_univ, Nat.card_eq_fintype_card] using hcapacity)
  exact (literal_restrict_projected_univ S B blockLabel).trans H
