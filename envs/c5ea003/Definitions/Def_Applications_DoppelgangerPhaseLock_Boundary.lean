-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Boundary
-- name    : Applications_DoppelgangerPhaseLock_Boundary
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:42:18.315733+00:00
-- url     : https://prove2.me/theorems/ca787c32-0cd2-4753-aa03-8fccf559293d
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Boundary
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Boundary`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Boundary.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
/-
# Doppelgänger Phase-Lock — boundaries of the phenomenon

The synchronization theorem of `Applications.DoppelgangerPhaseLock.Finite` is only
half of the story.  Adversarial review demands the *negative* half: which hypotheses
are genuinely needed, and what does the phenomenon **not** allow?

This file provides three sharp boundary results.

* **Reversibility obstruction.** If every stimulus acts on the internal state space by
  an injective map ("unitary"/reversible agents), phase-lock is impossible as soon as
  the agent has two distinct states.  Telepathic synchronization therefore *requires
  dissipative* (information-destroying) internal dynamics.  Concretely, the parity
  agent `s ↦ !s` never locks, while the "copy the stimulus" agent locks after one
  observation.

* **Identical stimuli are indispensable.** Modelling the two separated agents as a
  product automaton driven by a pair of stimulus streams, we show a concrete pair of
  states and of stimulus streams for which the agents never synchronize.

* **No signalling.** In the product automaton the second agent's state depends only on
  *its own* stimuli and its own initial state.  Phase-lock is therefore *not* a channel:
  nothing that happens at agent 1 can be detected at agent 2.  "Quantum telepathy" here
  is a shared-cause correlation, not communication.
-/

namespace Doppelganger

variable {S I : Type*}

/-! ### Reversible agents never phase-lock -/




/-- The parity agent: every stimulus flips its internal bit. -/
def parityAgent : Bool → Unit → Bool := fun s _ => !s



/-- The "copy the stimulus" agent: it overwrites its state with what it observes. -/
def copyAgent : Bool → Bool → Bool := fun _ i => i



/-! ### The product automaton: two agents, two stimulus streams -/

/-- The joint dynamics of the two spatially separated agents, each driven by its own
local stimulus. -/
def prodStep (δ : S → I → S) : S × S → I × I → S × S :=
  fun p q => (δ p.1 q.1, δ p.2 q.2)






/-! ### Finiteness is indispensable -/

/-- The **countdown agent** on an infinite state space: every stimulus decreases the
internal counter by one (and `0` is absorbing). -/
def countdownAgent : ℕ → Unit → ℕ := fun s _ => s - 1





end Doppelganger


