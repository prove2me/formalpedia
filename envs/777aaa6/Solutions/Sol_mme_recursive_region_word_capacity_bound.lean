-- Prove2me | solution 1 for mme_recursive_region_word_capacity_bound
-- status  : ACCEPTED   (prove)
-- author  : @raresbuhai
-- created : 2026-09-13T17:17:14.278224+00:00
-- url     : https://prove2.me/submissions/d700cdca-ba5d-4c18-88f1-38ec928e7f39

import Definitions.Def_mme_recursive_yz_CW_cells
import Mathlib.Tactic

open BigOperators MME MME.RecursiveYZ MME.RecursiveYZ.CWCells MME.CompleteSplit
open scoped Classical
set_option autoImplicit false
set_option maxHeartbeats 600000

theorem solution {P C : Type*} [Fintype P]
    (ell : ℕ) (cell : P → C) (shape : C → Fin 3 → ℕ)
    (mu : Fin 3 → C → CompleteWord ell → ℕ) :
    (∏ i : Fin 3, Nat.card (Block ell cell shape mu i)) ≤
      7 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
  classical
  have hi (i : Fin 3) : Nat.card (Block ell cell shape mu i) ≤
      3 ^ (Fintype.card P * 2 ^ (ell - 1)) := by
    have h := Nat.card_le_card_of_injective
      (fun f : Block ell cell shape mu i ↦ f.val) Subtype.val_injective
    simpa only [Nat.card_eq_fintype_card, Fintype.card_fun, CompleteWord, Fintype.card_fin,
      ← pow_mul, Nat.mul_comm] using h
  calc
    _ ≤ ∏ _i : Fin 3, 3 ^ (Fintype.card P * 2 ^ (ell - 1)) :=
      Finset.prod_le_prod (fun _ _ ↦ Nat.zero_le _) (fun i _ ↦ hi i)
    _ = 3 ^ (3 * (Fintype.card P * 2 ^ (ell - 1))) := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
      rw [Nat.mul_comm]
    _ ≤ _ := Nat.pow_le_pow_left (by decide : 3 ≤ 7) _
