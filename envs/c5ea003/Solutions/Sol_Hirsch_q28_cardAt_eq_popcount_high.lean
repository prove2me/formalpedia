-- Prove2me | solution 1 for Hirsch.q28_cardAt_eq_popcount_high
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T01:34:16.201655+00:00
-- url     : https://prove2.me/submissions/19712171-3be9-4935-9380-0a716ef33be0

import Mathlib
import Definitions.Def_Hirsch_q28_cert

open Hirsch

set_option maxHeartbeats 8000000

theorem solution :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      10 ≤ o1.val →
        commonActiveCard o1 o2 s =
          popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by
  intro o1
  fin_cases o1 <;> decide
