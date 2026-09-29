-- Prove2me | solution 1 for mme_binary_bidirectional_paired_diagonal_subset_card_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-27T12:22:20.836655+00:00
-- url     : https://prove2.me/submissions/0f1533b3-a413-42a2-bca4-90e035bf7d29

import Mathlib.Data.Finset.Card
import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

private theorem binary_bidirectional_paired_support_product_complete
    (R : Fin 2 → Fin 2 → Fin 2 → Prop)
    (h000 : R 0 0 0) (h001 : R 0 0 1)
    (h110 : R 1 1 0) (h111 : R 1 1 1)
    (k : ℕ) (u v : Fin k → Fin 2) :
    ∀ i, R (u i) (u i) (v i) := by
  have hbase : ∀ a b : Fin 2, R a a b := by
    intro a b
    fin_cases a <;> fin_cases b
    · exact h000
    · exact h001
    · exact h110
    · exact h111
  intro i
  exact hbase (u i) (v i)

theorem solution
    (R : Fin 2 → Fin 2 → Fin 2 → Prop)
    (h000 : R 0 0 0) (h001 : R 0 0 1)
    (h110 : R 1 1 0) (h111 : R 1 1 1)
    (k : ℕ) (P : Finset (Fin k → Fin 2))
    (hDiagonal : ∀ u ∈ P, ∀ v ∈ P,
      (∀ i, R (u i) (u i) (v i)) → u = v) :
    P.card ≤ 1 := by
  rw [Finset.card_le_one]
  intro u hu v hv
  exact hDiagonal u hu v hv
    (binary_bidirectional_paired_support_product_complete
      R h000 h001 h110 h111 k u v)
