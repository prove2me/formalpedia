-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form
-- name    : mme_stothers_phi233_cyclic_affine_hash_normal_form
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:28:55.066879+00:00
-- url     : https://prove2.me/theorems/04542ac7-81d6-4995-be7f-3fbd0c9827c4
-- title:
--   Linear normal form of the cyclic Phi233 affine hash
-- statement:
--   The cyclic Phi233 affine hash has an explicit linear form in every mode: $$H_i(e)=s+c_iq+\sum_{r,j}C_i(v_i(e))_{r,j}w_{r,j},\qquad(c_0,c_1,c_2)=(0,12,6).$$ The coefficient word depends only on the mode vertex. This normal form is the interface used to count one-edge retention fibers and two-edge collision fibers.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; affine hash expansion for Phi233.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

open BigOperators

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_affine_hash_normal_form
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta) :
    MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset i e =
      shift + (![0, 12 * offset, 6 * offset] : Fin 3 → ZMod p) i +
        ∑ r : Fin 3, ∑ j : Fin (2 * N),
          MME.StothersFourth.Phi233.cyclicHashModeCode p N i
            (MME.StothersFourth.Phi233.cyclicModeWord e i) r j * w r j := by
  sorry
