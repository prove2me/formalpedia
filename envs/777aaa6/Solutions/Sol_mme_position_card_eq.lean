-- Prove2me | solution 1 for mme_position_card_eq
-- status  : ACCEPTED   (prove)
-- author  : @Tamas Fulop
-- created : 2026-09-18T18:22:52.448482+00:00
-- url     : https://prove2.me/submissions/baf90cf0-034f-4281-b31a-a50af36bd490

import Definitions.Def_mme_recursive_yz_physical_words
import Mathlib.Tactic

open scoped BigOperators

set_option autoImplicit false

theorem solution : forall (R : Nat) (n : Fin R → Nat),
    Fintype.card (MME.RecursiveYZ.Position n) = 2 * ∑ r, n r := by
  intro R n
  unfold MME.RecursiveYZ.Position
  rw [Fintype.card_sigma]
  simp only [Fintype.card_prod, Fintype.card_fin]
  rw [← Finset.sum_mul, Nat.mul_comm]
