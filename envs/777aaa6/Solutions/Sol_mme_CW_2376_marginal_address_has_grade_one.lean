-- Prove2me | solution 1 for mme_CW_2376_marginal_address_has_grade_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-08-24T21:37:00.100927+00:00
-- url     : https://prove2.me/submissions/f2f788fc-249b-487b-a7e4-a0a04cdea5d9

import Definitions.Def_mme_CW_2376_marginal_support_hypergraph

open MME

set_option autoImplicit false

/-- Every mode word with the prescribed positive-scale CW marginal contains
a grade-one coordinate. -/
theorem solution
    (m : ℕ) (hm : 0 < m)
    (a : CW2376MarginalSupportedAddress m) (i : Fin 3) :
    ∃ j : Fin (cw2376ProfileLength m), a.1 i j = (1 : Fin 5) := by
  have hcard := a.2.2 i (1 : Fin 5)
  have hpos : 0 < (Finset.univ.filter
      (fun j => a.1 i j = (1 : Fin 5))).card := by
    rw [hcard]
    exact Nat.mul_pos (by norm_num) hm
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hpos
  exact ⟨j, (Finset.mem_filter.mp hj).2⟩
