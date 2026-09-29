-- Prove2me | solution 1 for mme_CW_q6_type2_cyclic_affine_hash_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T22:44:41.29277+00:00
-- url     : https://prove2.me/submissions/7a407c71-35a5-4327-9d18-cf6c78c7fac0

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_hash_mode_code
import Definitions.Def_mme_CW_q6_type2_cyclic_affine_hash

open MME BigOperators

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N L G : ℕ}
    (q : (Fin 3 → Fin (2 * N) → ZMod p) × ZMod p)
    (i : Fin 3) (e : CWQ6Type2CyclicEdge N L G) :
    cwQ6Type2CyclicAffineHash p N L G q i e =
      (if i = 0 then 0 else if i = 1 then 12 * q.2 else 6 * q.2) +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          cwQ6Type2CyclicHashModeCode p N i
            (cwQ6Type2CyclicModeWord e i) r j * q.1 r j := by
  fin_cases i
  · simp [cwQ6Type2CyclicAffineHash, cwQ6Type2CyclicHashModeCode,
      cwQ6Type2CyclicModeWord, cwQ6DoubledXHash, cwQ6DoubledYHash,
      cwQ6DoubledZHash, Fin.sum_univ_succ]
    simp only [mul_add, Finset.mul_sum]
    ring
  · simp [cwQ6Type2CyclicAffineHash, cwQ6Type2CyclicHashModeCode,
      cwQ6Type2CyclicModeWord, cwQ6DoubledXHash, cwQ6DoubledYHash,
      cwQ6DoubledZHash, Fin.sum_univ_succ]
    simp only [mul_add, Finset.mul_sum]
    ring
  · simp [cwQ6Type2CyclicAffineHash, cwQ6Type2CyclicHashModeCode,
      cwQ6Type2CyclicModeWord, cwQ6DoubledXHash, cwQ6DoubledYHash,
      cwQ6DoubledZHash, Fin.sum_univ_succ]
    ring
