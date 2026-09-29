-- Prove2me | Theorems.Thm_mme_stothers_phi233_cyclic_mode_word_tuple_injective
-- name    : mme_stothers_phi233_cyclic_mode_word_tuple_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-09-02T23:32:26.49771+00:00
-- url     : https://prove2.me/theorems/0591b220-6cd4-4ae9-8f59-b2834ed276b5
-- title:
--   The three cyclic mode words determine a Phi233 ambient edge
-- statement:
--   The ordered triple of cyclic mode vertices uniquely determines a Phi233 ambient edge. Equivalently, any two distinct ambient edges differ in at least one mode vertex. This selects the differing hash equation used to bound every non-diagonal collision pair.
-- source:
--   A. M. Davie and A. J. Stothers, Improved Bound for Complexity of Matrix Multiplication (2013), Section 5, pp. 365-367; cyclic Phi233 incidence structure.

import Mathlib.Tactic
import Definitions.Def_mme_stothers_phi233_cyclic_ambient_data

set_option autoImplicit false

theorem mme_stothers_phi233_cyclic_mode_word_tuple_injective :
    ∀ {N alpha beta gamma delta : ℕ},
      Function.Injective
        (MME.StothersFourth.Phi233.cyclicModeWord
          (N := N) (alpha := alpha) (beta := beta)
          (gamma := gamma) (delta := delta)) := by
  sorry
