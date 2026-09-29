-- Prove2me | Theorems.Thm_mme_CW_q6_type2_cyclic_supported_mix_closure
-- name    : mme_CW_q6_type2_cyclic_supported_mix_closure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T21:30:21.42267+00:00
-- url     : https://prove2.me/theorems/159cb657-f974-4b20-88cc-a05c76bec0bd
-- title:
--   Supported mixed cyclic vertices form an exact type-2 edge
-- statement:
--   Any coordinatewise-supported mixture of a mode-zero vertex, mode-one vertex, and mode-two vertex from three exact cyclic type-2 edges is itself the vertex triple of an exact cyclic type-2 edge. Thus the full exact-profile family is vertex-closed, the deterministic closure property needed by the Salem--Spencer pruning.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Lemma 3.3 and Section 3.2, pp. 356-360.

import Definitions.Def_mme_CW_q6_type2_cyclic_data

open MME

set_option autoImplicit false

theorem mme_CW_q6_type2_cyclic_supported_mix_closure
    {N L G : ℕ}
    (x y z : CWQ6Type2CyclicEdge N L G)
    (hsupport : CWQ6Type2CyclicCoordinatewiseSupported x y z) :
    ∃ e : CWQ6Type2CyclicEdge N L G,
      cwQ6Type2CyclicModeWord e 0 = cwQ6Type2CyclicModeWord x 0 ∧
      cwQ6Type2CyclicModeWord e 1 = cwQ6Type2CyclicModeWord y 1 ∧
      cwQ6Type2CyclicModeWord e 2 = cwQ6Type2CyclicModeWord z 2 := by
  sorry
