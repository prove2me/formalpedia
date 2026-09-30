-- Prove2me | solution 1 for Hirsch.q28_chamber_basis_certificate
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-05T23:20:30.060505+00:00
-- url     : https://prove2.me/submissions/8d0c7fab-4b66-45f2-be0a-54cb963831b2

import Mathlib
import Definitions.Def_Hirsch_model
import Definitions.Def_Hirsch_q28
import Definitions.Def_Hirsch_q28_cert
import Theorems.Thm_Hirsch_q28_chamber_ranks_low
import Theorems.Thm_Hirsch_q28_chamber_ranks_high

open scoped RealInnerProductSpace
open Hirsch

theorem solution :
    (∀ r : ℕ, r < 2002 → certOkUnrank r = true) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        unrank5 (combRank s0 s1 s2 s3 s4) = (s0, s1, s2, s3, s4)) ∧
    (∀ s0 s1 s2 s3 s4 : ℕ,
      s0 < s1 → s1 < s2 → s2 < s3 → s3 < s4 → s4 < 14 →
        combRank s0 s1 s2 s3 s4 < 2002) := by
  obtain ⟨hlow, hunrank, hranklt⟩ := q28_chamber_ranks_low
  refine ⟨?certs, hunrank, hranklt⟩
  intro r hr
  rcases Nat.lt_or_ge r 1100 with h | h
  · exact hlow r h
  · exact q28_chamber_ranks_high r h hr
