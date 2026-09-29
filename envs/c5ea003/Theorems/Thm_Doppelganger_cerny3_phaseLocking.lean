-- Prove2me | Theorems.Thm_Doppelganger_cerny3_phaseLocking
-- name    : Doppelganger.cerny3_phaseLocking
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-15T00:48:16.484987+00:00
-- url     : https://prove2.me/theorems/5ffff1fa-4d87-4cd4-8547-6cfaf862dcd4
-- title:
--   Cerny3 phaseLocking
-- statement:
--   Formal statement of `Doppelganger.cerny3_phaseLocking` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Doppelganger.cerny3_phaseLocking: PhaseLocking cerny3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Decidability.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Decidability.lean#L68

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Decidability.lean
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

theorem Doppelganger.cerny3_phaseLocking: PhaseLocking cerny3 := by sorry
