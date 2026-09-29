-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_mode_word_tuple_injective
-- name    : mme_CW_q6_type2_cyclic_mode_word_tuple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:00:07.955043+00:00
-- url     : https://prove2.me/theorems/e1b6791e-a8a2-4c5f-91f6-b8e250cf9d81
-- title:
--   The three cyclic mode words determine a q=6 type-2 edge
-- statement:
--   The ordered triple of cyclic mode vertices uniquely determines a cyclic q=6 type-2 edge. Equivalently, two distinct edges differ in at least one of their three mode words. This permits every non-diagonal collision pair to choose a mode with a nonzero hash-code difference.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 3.2, pp. 359-360; cyclic type-2 edge incidence structure.

import Mathlib
import Definitions.Def_mme_CW_q6_type2_cyclic_data

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_mode_word_tuple_injective :
    ∀ {N L G : ℕ},
      Function.Injective
        (fun e : CWQ6Type2CyclicEdge N L G ↦
          cwQ6Type2CyclicModeWord e) := by
  sorry
