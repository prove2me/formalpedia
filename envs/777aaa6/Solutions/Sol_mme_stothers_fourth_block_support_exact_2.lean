-- Prove2me | solution 2 for mme_stothers_fourth_block_support_exact
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-09-02T20:07:40.440444+00:00
-- url     : https://prove2.me/submissions/15b7c1d6-cf5f-4259-bb76-05cc6b731c69

import Theorems.Thm_mme_CW_fourth_canonical_support_exact

open BigOperators

universe u

set_option autoImplicit false

theorem solution
    {K : Type u} [Field K] :
    ∀ sigma : Fin 3 → Fin 9,
      (MME.StothersFourth.cwFourthCanonicalGrading K 6).blockTensor sigma = 0 ↔
        (∑ s, (sigma s).val) ≠ 8 := by
  exact mme_CW_fourth_canonical_support_exact 6 (0 : Fin 6)
