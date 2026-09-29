-- Prove2me | solution 1 for mme_dwz_prescribed_Z_power_uniform_basis_shuffle
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-17T08:18:18.238382+00:00
-- url     : https://prove2.me/submissions/d3dc5dc9-1d6b-49e6-b7f6-397b7227bbe0

import Definitions.Def_mme_dwz_prescribed_z_split_value
import Definitions.Def_mme_kron_pow_word_reindex
import Theorems.Thm_mme_dwz_available_block_shuffle_of_pretransitive_action
import Theorems.Thm_mme_kronPow_position_permutation_linear_equiv
import Theorems.Thm_mme_kronPow_position_permutation_recursive_basis
import Theorems.Thm_mme_basisZAllowedSubtensor_projection_certificate
import Theorems.Thm_mme_basisAllAllowedSubtensor_basis_equiv_transport
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Fintype.EquivFin
import Mathlib.LinearAlgebra.Basis.Submodule

open MME MME.TensorObj MME.DWZComponentRestriction MME.DWZRestrictedValue
  MME.DWZSquare Module PiTensorProduct
open scoped Classical

universe u
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

namespace MME.DWZProfileShuffle

theorem leftGradeCount_reindex {ι : Type u} {t n : ℕ}
    (grade : ι → Fin t) (w : PowIndex ι n) (a : Fin t)
    (e : Equiv.Perm (Fin n)) :
    leftGradeCount grade (PowIndex.reindex e w) a = leftGradeCount grade w a := by
  classical
  unfold leftGradeCount
  simp only [PowIndex.get_reindex]
  apply Finset.card_bij (fun r _ ↦ e r)
  · intro r hr
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hr
  · intro r _ s _ hrs
    exact e.injective hrs
  · intro r hr
    refine ⟨e.symm r, ?_, e.apply_symm_apply r⟩
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and, e.apply_symm_apply] using hr

theorem prescribedZWord_reindex_iff {ι : Type u} {t : ℕ}
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (m : ℕ)
    (e : Equiv.Perm (Fin (p.length m))) (w : PowIndex ι (p.length m)) :
    prescribedZWord grade p m (PowIndex.reindex e w) ↔ prescribedZWord grade p m w := by
  simp only [prescribedZWord, leftGradeCount_reindex]

/-- The inverse convention makes these shuffles a left group action. -/
def coordPerm {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) (e : Equiv.Perm (Fin (p.length m))) :
    Equiv.Perm {w : PowIndex ι (p.length m) // prescribedZWord grade p m w} where
  toFun w := ⟨PowIndex.reindex e.symm w.1,
    (prescribedZWord_reindex_iff grade p m e.symm w.1).2 w.2⟩
  invFun w := ⟨PowIndex.reindex e w.1,
    (prescribedZWord_reindex_iff grade p m e w.1).2 w.2⟩
  left_inv w := by
    apply Subtype.ext
    exact PowIndex.reindex_symm_reindex e.symm w.1
  right_inv w := by
    apply Subtype.ext
    exact PowIndex.reindex_symm_reindex e w.1

def blockLabel {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ)
    (w : {w : PowIndex ι (p.length m) // prescribedZWord grade p m w}) :
    {v : PowIndex (Fin t) (p.length m) // prescribedZWord id p m v} :=
  ⟨PowIndex.ofFun (p.length m) (fun r ↦ grade (PowIndex.get (p.length m) w.1 r)), by
    simpa only [prescribedZWord, leftGradeCount, PowIndex.get_ofFun, id_eq] using w.2⟩

theorem blockLabel_coordPerm {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) (e : Equiv.Perm (Fin (p.length m)))
    (w : {w : PowIndex ι (p.length m) // prescribedZWord grade p m w}) :
    blockLabel grade p m (coordPerm grade p m e w) =
      coordPerm id p m e (blockLabel grade p m w) := by
  apply Subtype.ext
  apply (PowIndex.equivFun (Fin t) (p.length m)).injective
  funext r
  simp [blockLabel, coordPerm, PowIndex.equivFun]

instance coordAction {ι : Type u} {t : ℕ} (grade : ι → Fin t)
    (p : IntegerZSplitProfile t) (m : ℕ) :
    MulAction (Equiv.Perm (Fin (p.length m)))
      {w : PowIndex ι (p.length m) // prescribedZWord grade p m w} where
  smul e w := coordPerm grade p m e w
  one_smul w := by
    change coordPerm grade p m 1 w = w
    apply Subtype.ext
    apply (PowIndex.equivFun ι (p.length m)).injective
    funext r
    simp [coordPerm, PowIndex.equivFun]
  mul_smul e f w := by
    change coordPerm grade p m (e * f) w = coordPerm grade p m e (coordPerm grade p m f w)
    apply Subtype.ext
    apply (PowIndex.equivFun ι (p.length m)).injective
    funext r
    simp only [coordPerm, Equiv.coe_fn_mk, PowIndex.equivFun, PowIndex.get_reindex]
    rfl

theorem block_action_pretransitive {t : ℕ} (p : IntegerZSplitProfile t) (m : ℕ) :
    MulAction.IsPretransitive (Equiv.Perm (Fin (p.length m)))
      {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w} := by
  classical
  refine ⟨?_⟩
  intro x y
  have hcard (a : Fin t) :
      Fintype.card {r : Fin (p.length m) // PowIndex.get (p.length m) x.1 r = a} =
      Fintype.card {r : Fin (p.length m) // PowIndex.get (p.length m) y.1 r = a} := by
    simpa only [Fintype.card_subtype, leftGradeCount, id_eq] using (x.2 a).trans (y.2 a).symm
  let fibers := fun a ↦ Fintype.equivOfCardEq (hcard a)
  let e := Equiv.ofFiberEquiv fibers
  refine ⟨e, ?_⟩
  apply Subtype.ext
  apply (PowIndex.equivFun (Fin t) (p.length m)).injective
  funext r
  change PowIndex.get (p.length m) (PowIndex.reindex e.symm x.1) r =
    PowIndex.get (p.length m) y.1 r
  simp only [PowIndex.get_reindex]
  have h := Equiv.ofFiberEquiv_map fibers (e.symm r)
  simpa only [e, Equiv.apply_symm_apply] using h.symm

theorem exact_profile_uniform_shuffle {t : ℕ} (p : IntegerZSplitProfile t) (m : ℕ) :
    ∃ system : AvailableBlockShuffle
      {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w}
      (Equiv.Perm (Fin (p.length m))),
      ∀ e w, (system.move e w).1 = PowIndex.reindex e.symm w.1 := by
  classical
  letI := block_action_pretransitive p m
  obtain ⟨system, hsystem⟩ := mme_dwz_available_block_shuffle_of_pretransitive_action
    {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w}
    (Equiv.Perm (Fin (p.length m)))
  refine ⟨system, ?_⟩
  intro e w
  rw [hsystem]
  rfl

theorem blockLabel_surjective_of_nonempty {ι : Type u} {t : ℕ}
    (grade : ι → Fin t) (p : IntegerZSplitProfile t) (m : ℕ)
    (hne : Nonempty {w : PowIndex ι (p.length m) // prescribedZWord grade p m w}) :
    Function.Surjective (blockLabel grade p m) := by
  classical
  obtain ⟨w⟩ := hne
  intro z
  obtain ⟨e, he⟩ := (block_action_pretransitive p m).exists_smul_eq
    (blockLabel grade p m w) z
  refine ⟨coordPerm grade p m e w, ?_⟩
  exact (blockLabel_coordPerm grade p m e w).trans he

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

theorem ambient_recursive_shuffle {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i))
    (n : ℕ) (e : Equiv.Perm (Fin n)) :
    ∃ Φ : ∀ i, (T.kronPow n).V i ≃ₗ[K] (T.kronPow n).V i,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (T.kronPow n).t =
        (T.kronPow n).t ∧
      ∀ i w, Φ i (kronPowModeBasis T i (b i) n w) =
        kronPowModeBasis T i (b i) n (PowIndex.reindex e w) := by
  obtain ⟨Φ, hb, ht⟩ := mme_kronPow_position_permutation_linear_equiv T b n e
  have hΦ (i : Fin 3) : Φ i = kronPowModePositionEquiv T i (b i) n e := by
    apply LinearEquiv.toLinearMap_injective
    apply (kronPowModeWordBasis T i (b i) n).ext
    intro w
    simpa [kronPowModePositionEquiv, kronPowWordReindex] using hb i w
  refine ⟨Φ, ht, ?_⟩
  intro i w
  rw [hΦ]
  exact mme_kronPow_position_permutation_recursive_basis T i (b i) n e w

theorem prescribed_power_shuffle {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i)) {t : ℕ}
    (grade : I 2 → Fin t) (p : IntegerZSplitProfile t) (m : ℕ)
    (e : Equiv.Perm (Fin (p.length m))) :
    let G := (T.kronPow (p.length m)).basisZAllowedGrading
      (kronPowModeBasis T 2 (b 2) (p.length m)) (prescribedZWord grade p m)
    ∃ Φ : ∀ i, G.classOf i 0 ≃ₗ[K] G.classOf i 0,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap)
        (prescribedZPower T (b 2) grade p m).t = (prescribedZPower T (b 2) grade p m).t ∧
      ∀ i w, Φ i (G.blockProj i 0 (kronPowModeBasis T i (b i) (p.length m) w)) =
        G.blockProj i 0 (kronPowModeBasis T i (b i) (p.length m)
          (PowIndex.reindex e.symm w)) := by
  classical
  let B := fun i ↦ kronPowModeBasis T i (b i) (p.length m)
  obtain ⟨E, ht, hb⟩ := ambient_recursive_shuffle T b (p.length m) e.symm
  let pe (i : Fin 3) : Equiv.Perm (PowIndex (I i) (p.length m)) :=
    { toFun := PowIndex.reindex e.symm
      invFun := PowIndex.reindex e
      left_inv := PowIndex.reindex_symm_reindex e.symm
      right_inv := PowIndex.reindex_symm_reindex e }
  have hp (i : Fin 3) (w : PowIndex (I i) (p.length m)) :
      zOnly (I := fun i ↦ PowIndex (I i) (p.length m)) (prescribedZWord grade p m) i w ↔
        zOnly (I := fun i ↦ PowIndex (I i) (p.length m)) (prescribedZWord grade p m) i (pe i w) := by
    by_cases hi : i = 2
    · subst i
      simpa only [zOnly, dif_pos rfl] using
        (prescribedZWord_reindex_iff grade p m e.symm w).symm
    · simp [zOnly, hi]
  have h := mme_basisAllAllowedSubtensor_basis_equiv_transport
    (T.kronPow (p.length m)) (T.kronPow (p.length m)) B B E pe hb ht
    (zOnly (prescribedZWord grade p m)) (zOnly (prescribedZWord grade p m)) hp
  have hG := zOnly_grading_eq (T.kronPow (p.length m)) B (prescribedZWord grade p m)
  let result (G : (T.kronPow (p.length m)).TypeGrading 2) : Prop :=
    ∃ Φ : ∀ i, G.classOf i 0 ≃ₗ[K] G.classOf i 0,
      PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (G.blockSubtensor (fun _ ↦ 0)).t =
        (G.blockSubtensor (fun _ ↦ 0)).t ∧
      ∀ i w, Φ i (G.blockProj i 0 (B i w)) = G.blockProj i 0 (B i (pe i w))
  have hr : result ((T.kronPow (p.length m)).basisAllAllowedGrading B
      (zOnly (prescribedZWord grade p m))) := by
    obtain ⟨Φ, hΦ, hBasis, _⟩ := h
    exact ⟨Φ, hΦ, hBasis⟩
  rw [hG] at hr
  exact hr

theorem exists_projected_basis {K : Type u} [Field K] (T : TensorObj K 3)
    {ι : Type u} (b : Basis ι K (T.V 2)) (allowed : ι → Prop) :
    ∃ B : Basis {a : ι // allowed a} K ((T.basisZAllowedGrading b allowed).classOf 2 0),
      ∀ a, (B a : T.V 2) = b a.1 := by
  classical
  let v : {a : ι // allowed a} → T.V 2 := fun a ↦ b a.1
  have hv : LinearIndependent K v := b.linearIndependent.comp _ Subtype.val_injective
  have hrange : Set.range v = b '' {a | allowed a} := by
    ext x
    constructor
    · rintro ⟨a, rfl⟩
      exact ⟨a.1, a.2, rfl⟩
    · rintro ⟨a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hspan : Submodule.span K (Set.range v) =
      (T.basisZAllowedGrading b allowed).classOf 2 0 := by
    rw [hrange]
    exact (mme_basisZAllowedSubtensor_projection_certificate T b allowed).2.2.2.symm
  refine ⟨(Basis.span hv).map (LinearEquiv.ofEq _ _ hspan), ?_⟩
  intro a
  simp [Basis.map_apply, v]

end MME.DWZProfileShuffle

theorem solution {K : Type u} [Field K] (T : TensorObj K 3)
    {I : Fin 3 → Type u} (b : ∀ i, Basis (I i) K (T.V i)) {t : ℕ}
    (grade : I 2 → Fin t) (p : IntegerZSplitProfile t) (m : ℕ) :
    let Coord := {w : PowIndex (I 2) (p.length m) // prescribedZWord grade p m w}
    let Block := {w : PowIndex (Fin t) (p.length m) // prescribedZWord id p m w}
    let S := prescribedZPower T (b 2) grade p m
    let G := (T.kronPow (p.length m)).basisZAllowedGrading
      (kronPowModeBasis T 2 (b 2) (p.length m)) (prescribedZWord grade p m)
    ∃ B : Basis Coord K (G.classOf 2 0),
    ∃ label : Coord → Block,
    ∃ system : AvailableBlockShuffle Block (Equiv.Perm (Fin (p.length m))),
      (∀ w, (B w : (T.kronPow (p.length m)).V 2) =
        kronPowModeBasis T 2 (b 2) (p.length m) w.1) ∧
      (∀ w, (label w).1 = PowIndex.ofFun (p.length m)
        (fun r ↦ grade (PowIndex.get (p.length m) w.1 r))) ∧
      (Nonempty Coord → Function.Surjective label) ∧
      (∀ e w, (system.move e w).1 = PowIndex.reindex e.symm w.1) ∧
      ∀ e : Equiv.Perm (Fin (p.length m)),
        ∃ Φ : ∀ i, G.classOf i 0 ≃ₗ[K] G.classOf i 0,
        ∃ perm : Equiv.Perm Coord,
          PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) S.t = S.t ∧
          (∀ w, (perm w).1 = PowIndex.reindex e.symm w.1) ∧
          (∀ w, Φ 2 (B w) = B (perm w)) ∧
          (∀ w, label (perm w) = system.move e (label w)) := by
  classical
  dsimp only
  let G := (T.kronPow (p.length m)).basisZAllowedGrading
    (kronPowModeBasis T 2 (b 2) (p.length m)) (prescribedZWord grade p m)
  obtain ⟨B, hB⟩ := MME.DWZProfileShuffle.exists_projected_basis
    (T.kronPow (p.length m)) (kronPowModeBasis T 2 (b 2) (p.length m))
    (prescribedZWord grade p m)
  obtain ⟨system, hsystem⟩ := MME.DWZProfileShuffle.exact_profile_uniform_shuffle p m
  refine ⟨B, MME.DWZProfileShuffle.blockLabel grade p m, system, hB,
    (fun _ ↦ rfl), MME.DWZProfileShuffle.blockLabel_surjective_of_nonempty grade p m,
    hsystem, ?_⟩
  intro e
  obtain ⟨Φ, ht, hΦ⟩ := MME.DWZProfileShuffle.prescribed_power_shuffle T b grade p m e
  refine ⟨Φ, MME.DWZProfileShuffle.coordPerm grade p m e, ht, (fun _ ↦ rfl), ?_, ?_⟩
  · have hproj (w : {w : PowIndex (I 2) (p.length m) // prescribedZWord grade p m w}) :
        G.blockProj 2 0 (kronPowModeBasis T 2 (b 2) (p.length m) w.1) = B w := by
      apply Subtype.ext
      have hm : kronPowModeBasis T 2 (b 2) (p.length m) w.1 ∈ G.classOf 2 0 := by
        rw [← hB w]
        exact (B w).property
      rw [TensorObj.TypeGrading.blockProj_apply_mem G 2 0 _ hm, hB]
    intro w
    rw [← hproj w, hΦ]
    exact hproj (MME.DWZProfileShuffle.coordPerm grade p m e w)
  · intro w
    apply Subtype.ext
    rw [hsystem]
    exact congrArg Subtype.val (MME.DWZProfileShuffle.blockLabel_coordPerm grade p m e w)
