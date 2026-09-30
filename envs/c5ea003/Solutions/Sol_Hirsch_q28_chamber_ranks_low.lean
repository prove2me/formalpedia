-- Prove2me | solution 1 for Hirsch.q28_chamber_ranks_low
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:32:52.440748+00:00
-- url     : https://prove2.me/submissions/832fe877-b1ac-4797-bc8b-b97afd34a306

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_chamber_ranks_0_1099
import Theorems.Thm_Hirsch_q28_combinadic_unrank

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    (∀ r : ℕ, r < 1100 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) :=
  ⟨q28_chamber_ranks_0_1099, q28_combinadic_unrank.1, q28_combinadic_unrank.2⟩
