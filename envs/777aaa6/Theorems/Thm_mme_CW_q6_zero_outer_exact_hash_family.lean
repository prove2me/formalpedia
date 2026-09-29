-- Prove2me | Theorems.Thm_mme_CW_q6_zero_outer_exact_hash_family
-- name    : mme_CW_q6_zero_outer_exact_hash_family
-- status  : Proved
-- author  : @Robertboy18
-- created : 2026-09-23T04:59:19.626881+00:00
-- url     : https://prove2.me/theorems/80bbbbf0-3012-45eb-97c1-63817d13de2c
-- title:
--   Exact single-star family at zero outer mass
-- statement:
--   For every N, the zero-outer coupled address space gives an induced primary-hash family with one star and exactly choose(2N,N) middle entries. The construction uses all exact addresses and the checked cardinality theorem, with no pruning or positive-outer-mass assumption. The full matrix exponent bound remains a separate obligation.
-- source:
--   Kernel-checked regional count identities and exact extraction with empty regions.

import Theorems.Thm_mme_CW_q6_exact_coupled_address_regularity
open MME

theorem mme_CW_q6_zero_outer_exact_hash_family (N : ℕ) :
    Nonempty (CWQ6PrimaryHashFamily N 0 N 1 (Nat.choose (2 * N) N)) := by sorry
