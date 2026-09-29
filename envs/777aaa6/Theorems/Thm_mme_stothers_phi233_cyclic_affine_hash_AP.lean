-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_affine_hash_AP
-- name    : mme_stothers_phi233_cyclic_affine_hash_AP
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:33:37.66156+00:00
-- url     : https://prove2.me/theorems/cc191ed4-1ecf-4a58-bbcd-5ebdf3495046
-- title:
--   Cyclic Phi233 affine-hash arithmetic progression
-- statement:
--   For every coordinatewise-supported mixture of three Phi233 cyclic ambient edges, the public affine hashes obey $$H_0(x)+H_1(y)=2H_2(z).$$ Therefore restricting all three vertex hashes to a lower-half three-term-progression-free label set preserves every ambient completion needed by induced-matching pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 5, pp. 356-360 and 365-367; cyclic Salem--Spencer hash identity.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_affine_hash

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_affine_hash_AP
    {p N alpha beta gamma delta : ℕ}
    (w : Fin 3 → Fin (2 * N) → ZMod p)
    (shift offset : ZMod p)
    (x y z : MME.StothersFourth.Phi233.CyclicAmbientEdge N alpha beta gamma delta)
    (hsupp : MME.StothersFourth.Phi233.CyclicCoordinatewiseSupported x y z) :
    MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset 0 x +
        MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset 1 y =
      2 * MME.StothersFourth.Phi233.cyclicAffineHash p N alpha beta gamma delta w shift offset 2 z := by
  sorry
