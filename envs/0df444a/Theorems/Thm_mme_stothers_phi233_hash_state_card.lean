-- Prove2me | Theorems.Thm_mme_stothers_phi233_hash_state_card
-- name    : mme_stothers_phi233_hash_state_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:14:51.867608+00:00
-- url     : https://prove2.me/theorems/ce514bbf-bc5d-4073-9582-d4c18f45e8d7
-- title:
--   Cardinality of the phi_233 affine hash-state space
-- statement:
--   For a prime $p$, the affine hash state used for the cyclic phi_233 construction has exactly $p^2p^{6N}$ elements. The factor $p^{6N}$ is the common pair-collision fiber scale, while the remaining factor $p^2$ is the normalized state-space factor appearing in the hashing budget.
-- source:
--   Finite affine hash-state count for the hashing construction in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 3.2.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_hash_state_instances

open MME

set_option autoImplicit false

theorem mme_stothers_phi233_hash_state_card
    (p N : ℕ) [Fact p.Prime] :
    Fintype.card (MME.StothersFourth.Phi233.HashState p N) =
      p ^ 2 * p ^ (6 * N) := by
  sorry
