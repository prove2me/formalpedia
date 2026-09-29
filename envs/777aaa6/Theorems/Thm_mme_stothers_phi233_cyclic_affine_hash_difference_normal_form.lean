-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
-- name    : mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:34:22.659361+00:00
-- url     : https://prove2.me/theorems/76c9e216-b8cc-49b8-bfd2-51ed728c728d
-- title:
--   Difference normal form for two Phi233 cyclic hashes
-- statement:
--   For two Phi233 ambient edges, subtracting their hashes in a fixed mode cancels the common shift and affine offset. The result is precisely the random weight word paired with the difference of their mode coefficient codes. This is the homogeneous linear equation governing collision fibers.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; affine collision equation.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e f : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta) :
    MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset i e -
        MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset i f =
      ∑ r : Fin 3, ∑ j : Fin (2 * N),
        (MME.StothersFourth.Phi233.cyclicHashModeCode p N i
              (MME.StothersFourth.Phi233.cyclicModeWord e i) r j -
            MME.StothersFourth.Phi233.cyclicHashModeCode p N i
              (MME.StothersFourth.Phi233.cyclicModeWord f i) r j) * w r j := by
  sorry
