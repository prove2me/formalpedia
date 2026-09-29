-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form
-- name    : mme_CW_q6_type2_cyclic_affine_hash_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:27:29.35209+00:00
-- url     : https://prove2.me/theorems/5fc8d62a-788a-44c4-acd6-adf72512dd48
-- title:
--   Exact linear-affine normal form of the cyclic q=6 type-2 hash
-- statement:
--   For the cyclic q=6 type-2 affine hash with base offsets $(2q,0,q)$, the three mode hashes have affine offsets $0$, $12q$, and $6q$. Their linear parts are exactly the weighted sums specified by the corresponding mode coefficient codes. This is the concrete normal form needed to apply the prime affine single-edge and collision-fiber estimates.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; expanded cyclic affine hash normal form.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_affine_hash_normal_form
    {p N L G : ℕ}
    (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p)
    (i : Fin 3) (e : CWQ6Type2CyclicEdge N L G) :
    cwQ6Type2CyclicAffineHash p N L G q i e =
      (if i = 0 then 0 else if i = 1 then 12 * q.2 else 6 * q.2) +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cwQ6Type2CyclicHashModeCode p N i
            (cwQ6Type2CyclicModeWord e i) r j * q.1 r j := by
  sorry
