-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
-- name    : mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T22:47:45.434797+00:00
-- url     : https://prove2.me/theorems/a7188801-bbac-4c09-b865-635d173afc15
-- title:
--   Homogeneous difference form for cyclic q=6 affine hashes
-- statement:
--   For two cyclic q=6 type-2 edges in the same mode, subtracting their affine hashes cancels the common mode offset. The difference is the homogeneous linear form obtained by multiplying each hash weight by the difference of the two corresponding coefficient codes. This gives the explicit collision equation used in the pair-fiber bound.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360; homogeneous collision equation for the cyclic hash.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form

open MME BigOperators

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
    {p N L G : ℕ}
    (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p)
    (i : Fin 3) (e f : CWQ6Type2CyclicEdge N L G) :
    cwQ6Type2CyclicAffineHash p N L G q i e -
        cwQ6Type2CyclicAffineHash p N L G q i f =
      ∑ r : Fin 3, ∑ j : Fin (2 * N),
        (cwQ6Type2CyclicHashModeCode p N i
              (cwQ6Type2CyclicModeWord e i) r j -
            cwQ6Type2CyclicHashModeCode p N i
              (cwQ6Type2CyclicModeWord f i) r j) * q.1 r j := by
  sorry
