-- Prove2me | solution 1 for mme_stothers_phi134_hash_state_card
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-05T10:34:18.622768+00:00
-- url     : https://prove2.me/submissions/ea487e0d-4afb-4cb8-857e-d9e37b761d1b

import Definitions.Def_mme_stothers_phi134_cyclic_hash_data

open MME.StothersFourth.Phi134

set_option autoImplicit false
set_option warningAsError true

theorem solution
    (p N : ℕ) [Fact p.Prime] :
    Fintype.card (HashState p N) = p ^ 2 * p ^ (6 * N) := by
  change Fintype.card
      (((((Fin 3 × Fin (2 * N)) ⊕ Unit) → ZMod p) × ZMod p)) = _
  simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_sum,
    Fintype.card_fin, Fintype.card_unit, ZMod.card]
  rw [show 3 * (2 * N) + 1 = 6 * N + 1 by omega]
  ring
