-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_affine_hash_AP
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:37:59.889286+00:00
-- url     : https://prove2.me/submissions/2c42d5f9-a056-4e84-a35a-345d7d785eea

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_doubled_hash_AP_identity

open MME

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ}
    (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p)
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupp : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    cwQ6Type2CyclicAffineHash p N L G q 0 x +
        cwQ6Type2CyclicAffineHash p N L G q 1 y =
      2 * cwQ6Type2CyclicAffineHash p N L G q 2 z := by
  let b : Fin 3 → ZMod p := ![2 * q.2, 0, q.2]
  have h := mme_CW_q6_type2_cyclic_doubled_hash_AP_identity
    b q.1 x y z hsupp
  simpa [cwQ6Type2CyclicAffineHash, b] using h
