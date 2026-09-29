-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_affine_hash_difference_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:50:43.731736+00:00
-- url     : https://prove2.me/submissions/6a564548-a044-4127-92f4-5fabd41e4189

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash
import Theorems.Thm_mme_CW_q6_type2_cyclic_affine_hash_normal_form

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
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
  rw [mme_CW_q6_type2_cyclic_affine_hash_normal_form q i e,
    mme_CW_q6_type2_cyclic_affine_hash_normal_form q i f]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring
