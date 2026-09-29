-- Prove2me | solution 1 for mme_Ctensor_balanced_word_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-25T02:00:39.272844+00:00
-- url     : https://prove2.me/submissions/79fa0969-b552-47d4-8a33-6bc64b53f605

import Theorems.Thm_mme_fintype_prescribed_fiber_function_card

open BigOperators

set_option autoImplicit false

theorem solution (H m : ℕ) :
    Nat.card
        {w : Fin (H * m) → Fin H // ∀ h,
          Fintype.card {j // w j = h} = m} =
      (H * m).factorial / ∏ _h : Fin H, m.factorial := by
  classical
  have hsum : (∑ _h : Fin H, m) = Fintype.card (Fin (H * m)) := by
    rw [Fintype.card_fin]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    exact nsmul_eq_mul H m
  letI : DecidablePred (fun g : Fin (H * m) → Fin H =>
      ∀ i : Fin H, Fintype.card {a // g a = i} = (fun _ : Fin H => m) i) :=
    fun _ => Fintype.decidableForallFintype
  have hcount := mme_fintype_prescribed_fiber_function_card
    (α := Fin (H * m)) (ι := Fin H) (fun _ => m) hsum
  rw [← Nat.card_eq_fintype_card] at hcount
  simpa only [Fintype.card_fin] using hcount
