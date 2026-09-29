-- Prove2me | Theorems.Thm_mme_CW_q6_exact_address_profile_sum
-- name    : mme_CW_q6_exact_address_profile_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-08-27T09:48:54.715483+00:00
-- url     : https://prove2.me/theorems/e860f11b-eb5a-43ef-af1d-71f79de58cc9
-- title:
--   An exact coupled q=6 address has a consistent profile sum
-- statement:
--   If a coupled q=6 address of length 2N has exact mode-zero and mode-one marginals (N,N,0), exact mode-two marginals (L,L,2G), and coordinatewise support contained in 000, 111, 012, and 102, then necessarily L+G=N. This is derived from the address itself, so no separate parameter-consistency hypothesis is required.
-- source:
--   D. Coppersmith and S. Winograd, Matrix Multiplication via Arithmetic Progressions, Journal of Symbolic Computation 9 (1990), exact coupled profile on pp. 270-271.

import Mathlib.Tactic
import Definitions.Def_mme_CW_q6_primary_hash_family

open MME

set_option autoImplicit false

theorem mme_CW_q6_exact_address_profile_sum
    {N L G : ℕ} (address : CWQ6ExactCoupledAddress N L G) :
    L + G = N := by
  sorry
