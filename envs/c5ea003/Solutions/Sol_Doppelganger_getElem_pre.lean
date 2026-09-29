-- Prove2me | solution 1 for Doppelganger.getElem_pre
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-19T16:38:37.692209+00:00
-- url     : https://prove2.me/submissions/82411a80-e2a1-423b-b776-23f6f976281e

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology

open Doppelganger

theorem solution {I : Type*} (y : ℕ → I) (n k : ℕ) (h : k < (pre y n).length) :
    (pre y n)[k] = y k := by
  simpa [pre] using List.getElem_ofFn (fun i : Fin n => y i) (h.trans_eq (by simp [pre]))
