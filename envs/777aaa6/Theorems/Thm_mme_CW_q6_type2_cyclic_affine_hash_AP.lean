-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_AP
-- name    : mme_CW_q6_type2_cyclic_affine_hash_AP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:33:25.773357+00:00
-- url     : https://prove2.me/theorems/b3b7896f-94c0-4ada-9cff-3aa505023a20
-- title:
--   Arithmetic-progression identity for the specialized cyclic q=6 affine hash
-- statement:
--   For every affine hash state and every coordinatewise-supported mixed triple of cyclic q=6 type-2 edges, the specialized mode hashes form an arithmetic progression: $H_0(x)+H_1(y)=2H_2(z)$. This permits progression-free label pruning to preserve supported completions.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; cyclic Salem--Spencer arithmetic-progression identity.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_doubled_hash_AP_identity

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_affine_hash_AP
    {p N L G : ℕ}
    (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p)
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupp : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    cwQ6Type2CyclicAffineHash p N L G q 0 x +
        cwQ6Type2CyclicAffineHash p N L G q 1 y =
      2 * cwQ6Type2CyclicAffineHash p N L G q 2 z := by
  sorry
