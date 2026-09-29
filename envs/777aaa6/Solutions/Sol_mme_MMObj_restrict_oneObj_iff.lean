-- Prove2me | solution 1 for mme_MMObj_restrict_oneObj_iff
-- status  : ACCEPTED   (prove)
-- author  : @Robertboy18
-- created : 2026-09-22T07:01:52.19313+00:00
-- url     : https://prove2.me/submissions/58a1bea6-81d9-4ff9-99c6-1f915de4cd36

import Theorems.Thm_mme_flatteningRank_MMObj_ab
import Theorems.Thm_mme_flatteningRank_MMObj_bc
import Mathlib.Tactic

open MME MME.TensorObj Module PiTensorProduct
universe u
set_option autoImplicit false

namespace MatrixRestrictionFromUnit

variable {K : Type u} [Field K]

lemma unit_flattening_rank_le_one (σ : MME.Split (Fin 3)) :
    flatteningRank σ (oneObj : TensorObj K 3) ≤ 1 := by
  classical
  let b := Basis.piTensorProduct
    (fun i : Sc σ ↦ Free.chooseBasis K ((oneObj : TensorObj K 3).V i))
  haveI := Module.Finite.of_basis b
  have hd : finrank K (PiTensorProduct K
      (fun i : Sc σ ↦ (oneObj : TensorObj K 3).V i)) ≤ 1 := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_pi]
    apply Finset.prod_le_one (fun _ _ ↦ Nat.zero_le _)
    intro i _
    rw [← Module.finrank_eq_card_basis
      (Free.chooseBasis K ((oneObj : TensorObj K 3).V i))]
    change finrank K K ≤ 1
    simp
  exact (Submodule.finrank_le _).trans hd

lemma volume_le_one {a b c : ℕ}
    (h : Restrict (MMObj K a b c) (oneObj : TensorObj K 3)) : a * b * c ≤ 1 := by
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  by_cases hc : c = 0
  · simp [hc]
  have hab := (mme_flatteningRank_MMObj_ab (K := K) a b c (by omega)).trans
    ((flatteningRank_mono _ h).trans (unit_flattening_rank_le_one _))
  have hbc := (mme_flatteningRank_MMObj_bc (K := K) a b c (by omega)).trans
    ((flatteningRank_mono _ h).trans (unit_flattening_rank_le_one _))
  have ha0 : 1 ≤ a := by omega
  have hb0 : 1 ≤ b := by omega
  have hc0 : 1 ≤ c := by omega
  have ha1 : a = 1 := by nlinarith
  have hb1 : b = 1 := by nlinarith
  have hc1 : c = 1 := by nlinarith
  simp [ha1, hb1, hc1]

set_option backward.isDefEq.respectTransparency false in
lemma restrict_of_volume_le_one (a b c : ℕ) (h : a * b * c ≤ 1) :
    Restrict (MMObj K a b c) (oneObj : TensorObj K 3) := by
  classical
  letI : ∀ _ : Fin 3, Module K K := fun _ ↦ inferInstance
  by_cases ha : a = 0
  · subst a
    letI : ∀ i : Fin 3, Module K (MMSpace K 0 b c i) := fun i ↦ MMSpace_module _ _ _ i
    refine ⟨fun _ ↦ 0, ?_⟩
    dsimp only [oneObj, MMObj]
    rw [PiTensorProduct.map_tprod]
    simp only [MMTensor, Finset.univ_eq_empty, Finset.sum_empty]
    exact (PiTensorProduct.tprod K).map_coord_zero 0 rfl
  by_cases hb : b = 0
  · subst b
    letI : ∀ i : Fin 3, Module K (MMSpace K a 0 c i) := fun i ↦ MMSpace_module _ _ _ i
    refine ⟨fun _ ↦ 0, ?_⟩
    dsimp only [oneObj, MMObj]
    rw [PiTensorProduct.map_tprod]
    simp only [MMTensor, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    exact (PiTensorProduct.tprod K).map_coord_zero 0 rfl
  by_cases hc : c = 0
  · subst c
    letI : ∀ i : Fin 3, Module K (MMSpace K a b 0 i) := fun i ↦ MMSpace_module _ _ _ i
    refine ⟨fun _ ↦ 0, ?_⟩
    dsimp only [oneObj, MMObj]
    rw [PiTensorProduct.map_tprod]
    simp only [MMTensor, Finset.univ_eq_empty, Finset.sum_empty, Finset.sum_const_zero]
    exact (PiTensorProduct.tprod K).map_coord_zero 0 rfl
  have ha0 : 1 ≤ a := by omega
  have hb0 : 1 ≤ b := by omega
  have hc0 : 1 ≤ c := by omega
  have hab : a * b ≤ 1 := (Nat.le_mul_of_pos_right (a * b) (by omega)).trans h
  have hc1 : c ≤ 1 := (Nat.le_mul_of_pos_left c (by positivity : 0 < a * b)).trans h
  have ha1 : a = 1 := by nlinarith
  have hb1 : b = 1 := by nlinarith
  have hc1 : c = 1 := by nlinarith
  subst a; subst b; subst c
  letI : ∀ i : Fin 3, Module K (MMSpace K 1 1 1 i) := fun i ↦ MMSpace_module _ _ _ i
  let v : ∀ i : Fin 3, (MMObj K 1 1 1).V i := fun i ↦
    match i with
    | ⟨0, _⟩ => Pi.single (0, 0) 1
    | ⟨1, _⟩ => Pi.single (0, 0) 1
    | ⟨2, _⟩ => Pi.single (0, 0) 1
  refine ⟨fun i ↦ (LinearMap.id : K →ₗ[K] K).smulRight (v i), ?_⟩
  dsimp only [oneObj, MMObj]
  rw [PiTensorProduct.map_tprod]
  simp [MMTensor, v]
  rfl

end MatrixRestrictionFromUnit

/-- A matrix multiplication tensor is obtainable from a scalar exactly in volumes zero and one. -/
theorem solution {K : Type u} [Field K] (a b c : ℕ) :
    TensorObj.Restrict (MMObj K a b c) (TensorObj.oneObj : TensorObj K 3) ↔
      a * b * c ≤ 1 :=
  ⟨MatrixRestrictionFromUnit.volume_le_one,
    MatrixRestrictionFromUnit.restrict_of_volume_le_one a b c⟩

#print axioms solution
