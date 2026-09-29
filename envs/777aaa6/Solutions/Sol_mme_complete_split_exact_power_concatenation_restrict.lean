-- Prove2me | solution 1 for mme_complete_split_exact_power_concatenation_restrict
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-20T14:27:53.672984+00:00
-- url     : https://prove2.me/submissions/22cc1091-3f18-4451-9b64-29679ee6b999

import Definitions.Def_mme_complete_split_profile_projection
import Definitions.Def_mme_kron_pow_mode_word_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open MME MME.CompleteSplit MME.DWZComponentRestriction Module
open PiTensorProduct TensorProduct BigOperators
open scoped NNReal

universe u

set_option autoImplicit false

/-!
# Concatenation of exact complete-profile powers

Two words that are exactly `beta`-consistent at lengths `m` and `n` concatenate to a word that is
exactly `beta`-consistent at length `m + n`, because the letter counts add and the constraint is
linear in the length.  The tensor statement is the corresponding restriction; the mode-wise
splitting map is the same one used by the accepted prescribed-Z concatenation, taken in all three
modes rather than only in the Z mode.
-/

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

private theorem word_count_succ
    {ι : Type u} {ell n : ℕ} (label : ι → CompleteWord ell)
    (x : ι) (w : PowIndex ι n) (sigma : CompleteWord ell) :
    wordCount (N := n + 1) label (x, w) sigma =
      (if label x = sigma then 1 else 0) + wordCount label w sigma := by
  classical
  simp only [wordCount, Finset.card_filter, Fin.sum_univ_succ]
  rfl

/-- The mode-wise splitting map of a tensor power, together with the additivity of the letter
counts it induces in every mode. -/
private theorem split_power_all_counts
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell) (m n : ℕ) :
    ∃ f : ∀ i, (T.kronPow (m + n)).V i →ₗ[K]
        ((T.kronPow m).V i ⊗[K] (T.kronPow n).V i),
      PiTensorProduct.map f (T.kronPow (m + n)).t =
        interchange (T.kronPow m).t (T.kronPow n).t ∧
      ∀ (i : Fin 3) (w : PowIndex (ι i) (m + n)),
        ∃ x : PowIndex (ι i) m, ∃ y : PowIndex (ι i) n,
          (∀ sigma, wordCount (label i) w sigma =
            wordCount (label i) x sigma + wordCount (label i) y sigma) ∧
          f i (kronPowModeBasis T i (b i) (m + n) w) =
            kronPowModeBasis T i (b i) m x ⊗ₜ[K] kronPowModeBasis T i (b i) n y := by
  classical
  induction m with
  | zero =>
    rw [Nat.zero_add]
    refine ⟨fun i ↦ (TensorProduct.lid K ((T.kronPow n).V i)).symm.toLinearMap,
      map_lid_symm (T.kronPow n).t, ?_⟩
    intro i w
    refine ⟨PUnit.unit, w, ?_, ?_⟩
    · intro sigma
      simp [wordCount]
    · change (TensorProduct.lid K ((T.kronPow n).V i)).symm
        (kronPowModeBasis T i (b i) n w) =
        (Basis.singleton (PowIndex (ι i) 0) K) PUnit.unit ⊗ₜ[K]
          kronPowModeBasis T i (b i) n w
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
    · rintro i ⟨z, w⟩
      obtain ⟨x, y, hcount, hb⟩ := hw i w
      refine ⟨(z, x), y, ?_, ?_⟩
      · intro sigma
        rw [word_count_succ, word_count_succ, hcount]
        exact (Nat.add_assoc _ _ _).symm
      · simp only [kronPowModeBasis]
        change (TensorProduct.assoc K (T.V i) ((T.kronPow m).V i)
          ((T.kronPow n).V i)).symm
          (TensorProduct.map (LinearMap.id : T.V i →ₗ[K] T.V i) (f i)
            ((Basis.tensorProduct (b i) (kronPowModeBasis T i (b i) (m + n))) (z, w))) =
          ((Basis.tensorProduct (b i) (kronPowModeBasis T i (b i) m)) (z, x)) ⊗ₜ[K]
            kronPowModeBasis T i (b i) n y
        rw [Basis.tensorProduct_apply, Basis.tensorProduct_apply,
          TensorProduct.map_tmul, LinearMap.id_apply, hb,
          TensorProduct.assoc_symm_tmul]

private theorem disallowed_all_projection_zero
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i))
    (allowed : (i : Fin 3) → ι i → Prop)
    (i : Fin 3) (j : ι i) (hj : ¬ allowed i j) :
    (T.basisAllAllowedGrading b allowed).blockProj i 0 (b i j) = 0 := by
  classical
  let G := T.basisAllAllowedGrading b allowed
  have hx : b i j ∈ G.classOf i 1 := by
    change b i j ∈ cwBasisGrade (b i)
      (fun k ↦ if allowed i k then (0 : Fin 2) else 1) 1
    exact Submodule.subset_span
      ⟨j, by simp only [Set.mem_setOf_eq, if_neg hj], rfl⟩
  exact (G.is_internal i).ofBijective_coeLinearMap_of_mem_ne
    (show (1 : Fin 2) ≠ 0 by decide) hx

theorem solution
    {K : Type u} [Field K] (T : TensorObj K 3) {ι : Fin 3 → Type u}
    (b : (i : Fin 3) → Basis (ι i) K (T.V i)) {ell : ℕ}
    (label : (i : Fin 3) → ι i → CompleteWord ell)
    (beta : Fin 3 → Profile ell) (m n : ℕ) :
    TensorObj.Restrict
      (TensorObj.kron (restrictedPower T b label beta 0 m)
        (restrictedPower T b label beta 0 n))
      (restrictedPower T b label beta 0 (m + n)) := by
  classical
  unfold restrictedPower
  let M := T.kronPow m
  let N := T.kronPow n
  let bM := fun i ↦ kronPowModeBasis T i (b i) m
  let bN := fun i ↦ kronPowModeBasis T i (b i) n
  let GM := M.basisAllAllowedGrading bM (fun i ↦ ApproxConsistent (label i) (beta i) 0)
  let GN := N.basisAllAllowedGrading bN (fun i ↦ ApproxConsistent (label i) (beta i) 0)
  obtain ⟨f, hf, hw⟩ := split_power_all_counts T b label m n
  let maps := fun i ↦ (TensorProduct.map (GM.blockProj i 0) (GN.blockProj i 0)).comp (f i)
  refine mme_restrict_basisAllAllowedSubtensor_of_vanishes
    (T.kronPow (m + n))
    (TensorObj.kron (M.basisAllAllowedSubtensor bM
        (fun i ↦ ApproxConsistent (label i) (beta i) 0))
      (N.basisAllAllowedSubtensor bN
        (fun i ↦ ApproxConsistent (label i) (beta i) 0)))
    (fun i ↦ kronPowModeBasis T i (b i) (m + n))
    (fun i ↦ ApproxConsistent (label i) (beta i) 0) maps ?_ ?_
  · change PiTensorProduct.map
      (fun i ↦ (TensorProduct.map (GM.blockProj i 0) (GN.blockProj i 0)).comp (f i))
      (T.kronPow (m + n)).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply, hf, map_interchange]
    rfl
  · intro i w hnot
    obtain ⟨x, y, hcount, hb⟩ := hw i w
    have hbad : ¬ ApproxConsistent (label i) (beta i) 0 x ∨
        ¬ ApproxConsistent (label i) (beta i) 0 y := by
      by_contra h
      push_neg at h
      apply hnot
      intro sigma
      have hx := h.1 sigma
      have hy := h.2 sigma
      simp only [NNReal.coe_zero, mul_zero, abs_nonpos_iff, sub_eq_zero] at hx hy ⊢
      rw [hcount sigma]
      push_cast
      rw [hx, hy]
      ring
    change TensorProduct.map (GM.blockProj i 0) (GN.blockProj i 0)
      (f i (kronPowModeBasis T i (b i) (m + n) w)) = 0
    rw [hb, TensorProduct.map_tmul]
    rcases hbad with hx | hy
    · rw [disallowed_all_projection_zero M bM _ i x hx, zero_tmul]
    · rw [disallowed_all_projection_zero N bN _ i y hy, tmul_zero]
