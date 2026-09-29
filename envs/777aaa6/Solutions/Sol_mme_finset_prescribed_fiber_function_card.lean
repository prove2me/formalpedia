-- Prove2me | solution 1 for mme_finset_prescribed_fiber_function_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T19:30:26.109564+00:00
-- url     : https://prove2.me/submissions/e65bdb17-4bdd-48a6-825c-c869f41810c6

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Set.Card

open scoped BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {α ι : Type*} [Fintype α] [Fintype ι]
    [DecidableEq α] [DecidableEq ι]
    (k : ι → ℕ) (hsum : ∑ i, k i = Fintype.card α) :
    (Finset.univ.filter fun g : α → ι ↦
      ∀ i, Fintype.card {a // g a = i} = k i).card =
      Nat.multinomial Finset.univ k := by
  classical
  let P : (α → ι) → Prop := fun g ↦
    ∀ i, Fintype.card {a // g a = i} = k i
  have h := mme_fintype_prescribed_fiber_function_card k hsum
  calc
    (Finset.univ.filter fun g : α → ι ↦
        ∀ i, Fintype.card {a // g a = i} = k i).card =
        ({g : α → ι | P g} : Set (α → ι)).ncard := by
      rw [← Set.ncard_coe_finset]
      congr 1
      ext g
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and, Set.mem_setOf_eq, P]
    _ = Nat.card ({g : α → ι | P g} : Set (α → ι)) :=
      (Nat.card_coe_set_eq
        ({g : α → ι | P g} : Set (α → ι))).symm
    _ = Fintype.card
          {g : α → ι //
            ∀ i, Fintype.card {a // g a = i} = k i} := by
      change Nat.card {g // P g} = _
      rw [Nat.card_eq_fintype_card]
    _ = (Fintype.card α).factorial / ∏ i, (k i).factorial := h
    _ = Nat.multinomial Finset.univ k := by
      simp only [Nat.multinomial, hsum]
