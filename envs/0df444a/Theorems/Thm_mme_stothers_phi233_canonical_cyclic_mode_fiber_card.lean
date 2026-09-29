-- Prove2me | Theorems.Thm_mme_stothers_phi233_canonical_cyclic_mode_fiber_card
-- name    : mme_stothers_phi233_canonical_cyclic_mode_fiber_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-03T00:01:18.042291+00:00
-- url     : https://prove2.me/theorems/847d0e1e-8861-4c89-a9fa-c4de929f4ecc
-- title:
--   Cyclic phi_233 mode fibers are products of ordinary stars
-- statement:
--   Fix an exact phi_233 address and use it in all three cyclic copies. For any cyclic mode, the ambient fiber fixing the resulting cyclic vertex has cardinality equal to the product of the three ordinary same-marginal fixed-word stars, one from each mode. The analogous exact cyclic fiber is the product of the three ordinary exact-profile stars. Since every cyclic vertex contains exactly one word from each ordinary mode, the cyclic permutation changes only the order of the factors. This identifies the degree appearing in the cyclic hashing argument with the product controlled by the three one-mode completion estimates.
-- source:
--   The cyclic product construction in A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication, Proceedings of the Royal Society of Edinburgh A 143(2), 2013, Section 5.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

open MME BigOperators

set_option autoImplicit false
set_option maxRecDepth 10000

theorem mme_stothers_phi233_canonical_cyclic_mode_fiber_card
    (N alpha beta gamma delta : ℕ)
    (a : MME.StothersFourth.Phi233.ExactProfileAddress
      N alpha beta gamma delta) (i : Fin 3) :
    Nat.card
        {e : MME.StothersFourth.Phi233.CyclicAmbientEdge
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.cyclicModeWord e i =
            MME.StothersFourth.Phi233.cyclicModeWord
              (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.MarginalAddress
              N alpha beta gamma delta // b.1 l = a.1.1 l} ∧
    Nat.card
        {e : MME.StothersFourth.Phi233.CyclicExactEdge
            N alpha beta gamma delta //
          MME.StothersFourth.Phi233.cyclicModeWord
              (MME.StothersFourth.Phi233.exactToAmbient e) i =
            MME.StothersFourth.Phi233.cyclicModeWord
              (a.1, (a.1, a.1)) i} =
      ∏ l : Fin 3,
        Nat.card
          {b : MME.StothersFourth.Phi233.ExactProfileAddress
              N alpha beta gamma delta // b.1.1 l = a.1.1 l} := by
  sorry
