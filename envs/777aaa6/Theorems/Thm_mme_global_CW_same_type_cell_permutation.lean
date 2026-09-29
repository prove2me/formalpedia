-- Prove2me | Theorems.Thm_mme_global_CW_same_type_cell_permutation
-- name    : mme_global_CW_same_type_cell_permutation
-- status  : Proved
-- author  : @raresbuhai
-- created : 2026-09-22T07:12:30.641429+00:00
-- url     : https://prove2.me/theorems/f328aa47-57b2-4c1b-a6d5-f142d70e2a8d
-- title:
--   Global target addresses with the same joint type have equivalent cells
-- statement:
--   Any two original-block addresses with the same exact joint counts are related by a permutation of unpaired positions preserving their full cells. This supplies exact template normalization before hole repair.
-- source:
--   Finite global extraction for More Asymmetry Proposition 5.1 and Theorem 5.3.

import Definitions.Def_mme_global_CW_stage_data
import Mathlib
open BigOperators MME MME.RecursiveYZ MME.GlobalCW
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem cell_fiber {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (a : RecursiveXHash.Address degree R bounds n) (r : Fin R)
    (c : RecursiveThinSplit.Split degree (bounds r)) :
    Fintype.card {p : Place n // cell a p = ⟨r,c⟩} = RecursiveThinSplit.count (a r) c := by
  let e : {p : Place n // cell a p = ⟨r,c⟩} ≃ {t : Fin (n r) // a r t = c} := {
    toFun := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      exact ⟨t,eq_of_heq (Sigma.mk.inj hp).2⟩
    invFun := fun t ↦ ⟨⟨r,t.val⟩,by simp only [cell,t.property]⟩
    left_inv := by
      rintro ⟨⟨r',t⟩,hp⟩
      have hr : r' = r := congrArg Sigma.fst hp
      subst r'
      rfl
    right_inv := by intro t; rfl }
  rw [Fintype.card_congr e,Fintype.card_subtype]
  rfl

theorem mme_global_CW_same_type_cell_permutation {degree R : ℕ} {bounds : Fin R → Fin 3 → ℕ} {n : Fin R → ℕ}
    (m : ∀ r, RecursiveThinSplit.Split degree (bounds r) → ℕ)
    (a b : RecursiveXHash.Address degree R bounds n)
    (ha : a ∈ RecursiveXHash.target m) (hb : b ∈ RecursiveXHash.target m) :
    ∃ sigma : Equiv.Perm (Place n), ∀ p, cell a (sigma p) = cell b p := by
  sorry
