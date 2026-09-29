-- Prove2me | solution 1 for mme_recursive_yz_positions_from_parent_counts
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-27T17:03:35.490506+00:00
-- url     : https://prove2.me/submissions/d6165a74-e885-491d-81f6-da3484fcde86

import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Prod

open BigOperators MME.RecursiveYZ
set_option autoImplicit false

theorem solution {R P : ℕ} (n : Fin R → ℕ)
    (h : ∑ r : Fin R, n r = P) :
    Nonempty (Fin P ≃ ((r : Fin R) × Fin (n r))) ∧
      Nonempty (Fin (2 * P) ≃ Position n) := by
  classical
  have hrows : Fintype.card ((r : Fin R) × Fin (n r)) = P := by
    simpa only [Fintype.card_sigma, Fintype.card_fin] using h
  have hpositions : Fintype.card (Position n) = 2 * P := by
    calc
      Fintype.card (Position n) = ∑ r : Fin R, n r * 2 := by
        simp only [Position, Fintype.card_sigma, Fintype.card_prod, Fintype.card_fin]
      _ = (∑ r : Fin R, n r) * 2 := by rw [Finset.sum_mul]
      _ = 2 * P := by rw [h, Nat.mul_comm]
  constructor
  · exact ⟨(Fintype.equivFinOfCardEq hrows).symm⟩
  · exact ⟨(Fintype.equivFinOfCardEq hpositions).symm⟩
