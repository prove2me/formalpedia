-- Prove2me | solution 1 for Doppelganger.cerny3_phaseLocking
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-15T00:48:29.11379+00:00
-- url     : https://prove2.me/submissions/db1d4947-7a2a-4d09-93b5-4352a3e6f166

-- Sol generated from Applications/DoppelgangerPhaseLock/Decidability.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Boundary
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Decidability
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
/-
# Doppelgänger Phase-Lock — decidability and extremal experiments

Third research cycle.  The finite synchronization theorem is *effective*: because a
phase-locking agent must lock within `(|S| - 1)·|S|²` stimuli
(`Doppelganger.exists_lock_length_le_of_phaseLocking`), the search for a locking word can
be confined to a finite set.  This yields a genuine `Decidable` instance: *whether two
identical agents can be telepathically synchronized is an algorithmically decidable
property of the agent design*.

We then run the decision procedure as an experiment on the three-state Černý agent, and
prove — by exhaustive certified search — that its minimal phase-lock time is exactly
`4 = (3-1)²`, the Černý extremal value.  This is a genuine (kernel-checked, no
`native_decide`) computation, not a definitional triviality.

## Main results

* `Doppelganger.phaseLocking_iff_exists_bounded` — reduction to a finite search.
* `Doppelganger.decidablePhaseLocking` — decidability of doppelgänger telepathy.
* `Doppelganger.cerny3_lock_time_eq_four` — the Černý agent locks in exactly four shared
  stimuli, and in no fewer.
-/

open Doppelganger



variable {S I : Type*} [Fintype S] [DecidableEq S] [Fintype I] [DecidableEq I]




/-! ### Running the decision procedure -/




theorem cerny3_locks_baab : Locks cerny3 [1, 0, 0, 1] := by decide









open Doppelganger in
theorem solution: PhaseLocking cerny3 := ⟨_, cerny3_locks_baab⟩
