-- Prove2me | solution 1 for Hirsch.q28_cardAt_eq_popcount_low
-- status  : ACCEPTED   (prove)
-- author  : @jjosh
-- created : 2026-09-06T01:34:15.698052+00:00
-- url     : https://prove2.me/submissions/bea73a76-95af-4b99-ae43-3995fdc1443f

import Mathlib
import Definitions.Def_Hirsch_q28_cert

open Hirsch

set_option maxHeartbeats 8000000

theorem solution :
    ∀ (o1 o2 : Fin 20) (s : Fin 16),
      o1.val < 10 →
        commonActiveCard o1 o2 s =
          popcount28 (Nat.land (tightMask o1 0) (tightMask o2 s)) := by
  intro o1
  fin_cases o1 <;> decide
