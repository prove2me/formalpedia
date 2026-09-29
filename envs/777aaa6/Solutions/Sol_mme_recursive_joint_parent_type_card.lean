-- Prove2me | solution 1 for mme_recursive_joint_parent_type_card
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:31:21.724948+00:00
-- url     : https://prove2.me/submissions/64bfa43c-3974-4553-9bdc-e7c2ee9205d0

import Definitions.Def_mme_recursive_yz_hash_filter
import Theorems.Thm_mme_prescribed_cell_histogram_card
import Mathlib

open BigOperators MME.RecursiveYZ
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem solution {half R : ℕ} {n : Fin R → ℕ} {W : Type*} [Fintype W]
    (y : ∀ r, Fin (n r) → Fin (half + 1)) (f : Position n → W) :
    Nat.card {g : Position n → W // ParentType y (parentCounts y f) g} =
      ∏ r, histogramNumber (parentCounts y f r) := by
  classical
  let U (r : Fin R) := {g : Fin (n r) → (Fin 2 → W) // Useful (y r) (parentCounts y f r) g}
  let e : {g : Position n → W // ParentType y (parentCounts y f) g} ≃ (∀ r, U r) := {
    toFun := fun g r ↦ ⟨parentWord g.val r,g.property r⟩
    invFun := fun g ↦ ⟨fun p ↦ (g p.1).val p.2.1 p.2.2,fun r ↦ (g r).property⟩
    left_inv := fun g ↦ rfl
    right_inv := fun g ↦ rfl }
  rw [Nat.card_congr e,Nat.card_eq_fintype_card,Fintype.card_pi]
  apply Finset.prod_congr rfl
  intro r hr
  have hm j : ∑ w, parentCounts y f r j w = Fintype.card {t : Fin (n r) // y r t = j} := by
    have hc := Finset.card_eq_sum_card_fiberwise
      (s := Finset.univ.filter (fun t : Fin (n r) ↦ y r t = j))
      (t := (Finset.univ : Finset (Fin 2 → W)))
      (f := parentWord f r) (fun _ _ ↦ Finset.mem_univ _)
    convert hc.symm using 1 <;>
      simp only [parentCounts,count,Finset.filter_filter,Fintype.card_subtype]
    apply Finset.sum_congr
    · ext w; simp only [Finset.mem_univ]
    intro w hw
    apply congrArg Finset.card
    ext t
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
  have hc := mme_prescribed_cell_histogram_card (y r) (parentCounts y f r)
    (by intro j; simpa only [← Nat.card_eq_fintype_card] using hm j)
  simp only [← Nat.card_eq_fintype_card] at hc ⊢
  rw [hc]
  unfold histogramNumber
  apply Finset.prod_congr rfl
  intro j hj
  rw [hm]
  simp only [← Nat.card_eq_fintype_card]
