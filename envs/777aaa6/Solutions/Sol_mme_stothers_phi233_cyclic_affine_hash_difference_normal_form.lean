-- Prove2me | solution 1 for mme_stothers_phi233_cyclic_affine_hash_difference_normal_form
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T23:34:55.407466+00:00
-- url     : https://prove2.me/submissions/4c7a6ff4-552e-468b-a7af-8146a8df566b

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash
import Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_normal_form

open BigOperators
open MME.StothersFourth.Phi233

set_option autoImplicit false
set_option warningAsError true

theorem solution
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p) (i : Fin 3)
    (e f : CyclicAmbientEdge N alpha beta gamma delta) :
    cyclicAffineHash p N alpha beta gamma delta w shift offset i e -
        cyclicAffineHash p N alpha beta gamma delta w shift offset i f =
      ∑ r : Fin 3, ∑ j : Fin (2 * N),
        (cyclicHashModeCode p N i (cyclicModeWord e i) r j -
          cyclicHashModeCode p N i (cyclicModeWord f i) r j) * w r j := by
  rw [mme_stothers_phi233_cyclic_affine_hash_normal_form w shift offset i e,
    mme_stothers_phi233_cyclic_affine_hash_normal_form w shift offset i f]
  simp_rw [sub_mul, Finset.sum_sub_distrib]
  ring
