-- Prove2me | solution 1 for mme_recursive_yz_actual_cell_product_restriction
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T12:09:11.629795+00:00
-- url     : https://prove2.me/submissions/ccdf3a67-32c0-4fea-be39-3b1082623cab

import Definitions.Def_mme_recursive_yz_cell_partition
import Definitions.Def_mme_kronFin_family_mode_map_basis_data
import Theorems.Thm_mme_kronPow_fiber_grouping_preserves_tensor_and_basis
import Theorems.Thm_mme_restrict_basisAllAllowedSubtensor_of_vanishes

open BigOperators MME MME.TensorObj MME.RecursiveYZ MME.RecursiveYZ.CWCells
  MME.CompleteSplit Module PiTensorProduct
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1600000
universe u v w

private theorem count_fiber {P : Type v} {C W : Type*} [Fintype P]
    {cell : P → C} (D : Partition cell) (f : P → W)
    (j : Fin D.parts) (a : W) :
    MME.RecursiveYZ.count cell f (D.cells j) a =
      MME.RecursiveYZ.count (fun _ : Fin (D.size j) ↦ Unit.unit)
        (fun r ↦ f (D.fiber j r).val) Unit.unit a := by
  classical
  unfold MME.RecursiveYZ.count
  simp only [true_and]
  symm
  apply Finset.card_bij (fun r _ ↦ (D.fiber j r).val)
  · intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact ⟨(D.fiber j r).property, hr⟩
  · intro r hr s hs heq
    exact (D.fiber j).injective (Subtype.ext heq)
  · intro p hp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp
    let x : {p : P // cell p = D.cells j} := ⟨p, hp.1⟩
    refine ⟨(D.fiber j).symm x, ?_, ?_⟩
    · simpa only [Finset.mem_filter, Finset.mem_univ, true_and,
        Equiv.apply_symm_apply] using hp.2
    · exact congrArg Subtype.val ((D.fiber j).apply_symm_apply x)

private theorem label_fiber {P : Type v} {C : Type w} {cell : P → C}
    (D : Partition cell) (q ell L : ℕ) (e : Fin L ≃ P)
    (x : WordIndex.{u} q ell L) (j : Fin D.parts) (r : Fin (D.size j)) :
    label q ell (D.size j) (Equiv.refl _)
      (fun a ↦ x (D.leaves ell L e ⟨j,a⟩)) r =
    label q ell L e x (D.fiber j r).val := by
  funext s
  simp [label, Partition.leaves]

private theorem allowed_of_fibers {P : Type v} {C : Type w} [Fintype P]
    {cell : P → C} (D : Partition cell) (q ell L : ℕ) (e : Fin L ≃ P)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (i : Fin 3) (x : WordIndex.{u} q ell L)
    (h : ∀ j, allowed q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ ↦ shape (D.cells j)) (fun a _ ↦ mu a (D.cells j)) i
      (fun a ↦ x (D.leaves ell L e ⟨j,a⟩))) :
    allowed q ell L e cell shape mu i x := by
  constructor
  · intro p
    obtain ⟨⟨j,r⟩, hp⟩ := D.positions.surjective p
    have hc : cell (D.fiber j r).val = D.cells j := (D.fiber j r).property
    have hg := (h j).1 r
    rw [label_fiber] at hg
    change D.positions ⟨j,r⟩ = p at hp
    rw [Partition.positions_apply] at hp
    simpa only [hp, ← hc] using hg
  · intro c a
    obtain ⟨j,rfl⟩ := D.cells.surjective c
    rw [count_fiber]
    have hh := (h j).2 Unit.unit a
    have hl : label q ell (D.size j) (Equiv.refl _)
        (fun a ↦ x (D.leaves ell L e ⟨j,a⟩)) =
        (fun r ↦ label q ell L e x (D.fiber j r).val) := by
      funext r; exact label_fiber D q ell L e x j r
    rw [hl] at hh
    exact hh

theorem solution {K : Type u} [Field K] {P : Type v} {C : Type w} [Fintype P]
    (q ell L : ℕ) (positions : Fin L ≃ P) (cell : P → C)
    (shape : C → Fin 3 → ℕ) (mu : Fin 3 → C → CompleteWord ell → ℕ)
    (D : Partition cell) :
    Restrict (kronFin D.parts (D.piece K q ell shape mu))
      (unbroken K q ell L positions cell shape mu) := by
  classical
  let raw := fun j : Fin D.parts ↦ source K q ell (D.size j)
  let child := D.piece K q ell shape mu
  let G := fun j : Fin D.parts ↦
    grading K q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
      (fun _ ↦ shape (D.cells j)) (fun i _ ↦ mu i (D.cells j))
  let proj := fun j i ↦ (G j).blockProj i 0
  obtain ⟨Φ, ht, hb⟩ := mme_kronPow_fiber_grouping_preserves_tensor_and_basis
    (CWObj K q) (fun i ↦ (MME.DWZStep1Support.cwThreeCanonicalBasis K q i).reindex Equiv.ulift.symm)
    (fun j ↦ D.size j * 2 ^ (ell - 1)) (D.leaves ell L positions).symm
  change PiTensorProduct.map (fun i ↦ (Φ i).toLinearMap) (source K q ell L).t =
    (kronFin D.parts raw).t at ht
  have hB (i : Fin 3) (x : WordIndex.{u} q ell L) :
      Φ i (basis K q ell L i x) =
        kronFinModePiBasis D.parts raw i (fun j ↦ basis K q ell (D.size j) i)
          (fun j a ↦ x (D.leaves ell L positions ⟨j,a⟩)) := hb i x
  let F := fun i ↦ (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap
  apply mme_restrict_basisAllAllowedSubtensor_of_vanishes (source K q ell L)
    (kronFin D.parts child) (basis K q ell L)
    (allowed q ell L positions cell shape mu) F
  · change PiTensorProduct.map (fun i ↦
      (kronFinFamilyModeMap D.parts raw child proj i).comp (Φ i).toLinearMap)
        (source K q ell L).t = _
    rw [PiTensorProduct.map_comp, LinearMap.comp_apply]
    exact (congrArg (PiTensorProduct.map
      (kronFinFamilyModeMap D.parts raw child proj)) ht).trans
      (kronFinFamilyModeMap_preserves_tensor raw child proj (fun _ ↦ rfl))
  · intro i x hx
    change kronFinFamilyModeMap D.parts raw child proj i
      (Φ i (basis K q ell L i x)) = 0
    rw [hB]
    apply kronFinFamilyModeMap_basis_eq_zero_of_exists raw child i
      (fun j ↦ basis K q ell (D.size j) i) proj
    have hn : ¬ ∀ j, allowed q ell (D.size j) (Equiv.refl _) (fun _ ↦ Unit.unit)
        (fun _ ↦ shape (D.cells j)) (fun a _ ↦ mu a (D.cells j)) i
        (fun a ↦ x (D.leaves ell L positions ⟨j,a⟩)) :=
      fun h ↦ hx (allowed_of_fibers D q ell L positions shape mu i x h)
    obtain ⟨j,hj⟩ := not_forall.mp hn
    refine ⟨j, ?_⟩
    apply TensorObj.TypeGrading.blockProj_apply_mem_ne (G j) i 0 1 (by decide)
    change basis K q ell (D.size j) i _ ∈ Submodule.span K
      (basis K q ell (D.size j) i '' {w | (if allowed q ell (D.size j) (Equiv.refl _)
        (fun _ ↦ Unit.unit) (fun _ ↦ shape (D.cells j))
        (fun a _ ↦ mu a (D.cells j)) i w then (0 : Fin 2) else 1) = 1})
    exact Submodule.subset_span
      ⟨(fun a ↦ x (D.leaves ell L positions ⟨j,a⟩)), if_neg hj, rfl⟩
