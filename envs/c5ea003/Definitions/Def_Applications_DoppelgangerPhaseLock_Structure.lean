-- Prove2me | Definitions.Def_Applications_DoppelgangerPhaseLock_Structure
-- name    : Applications_DoppelgangerPhaseLock_Structure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:44:27.585529+00:00
-- url     : https://prove2.me/theorems/71f05c7e-3229-4e6c-8c70-56f662c5a918
-- title:
--   Aether Catalog definitions — Applications_DoppelgangerPhaseLock_Structure
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.DoppelgangerPhaseLock.Structure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/DoppelgangerPhaseLock/Structure.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Finite
/-
# Doppelgänger Phase-Lock — structural calculus of phase-locking agents

Second research cycle.  Having established *when* phase-lock happens, we ask how the
property behaves under the natural constructions on agents: parallel composition,
coarse-graining (simulation/quotient), relabelling of the stimulus alphabet, and order
structure on the internal state space.

## Main results

* `Doppelganger.phaseLocking_par` — **compositional telepathy**: two independent
  phase-locking subsystems observing the same environment lock jointly, and the joint
  locking time is at most the sum of the individual ones (`Doppelganger.locks_par`).
* `Doppelganger.locks_of_simulation` — **coarse-graining preserves telepathy**: a
  surjective simulation (a homomorphic image of the agent) inherits every locking word.
* `Doppelganger.locks_relabel_iff` — functoriality in the stimulus alphabet.
* `Doppelganger.monotone_locks_iff` — **order rigidity**: for an agent whose every
  stimulus acts monotonically on a linearly ordered state space, locking the two *extreme*
  states already locks *all* states.  Consequently
  `Doppelganger.monotone_lock_length` gives a *quadratic* phase-lock time for monotone
  agents, improving the general cubic bound
  `Doppelganger.exists_lock_length_le_of_phaseLocking`.
-/

namespace Doppelganger

variable {S S' I I' : Type*}

/-! ### Parallel composition of agents -/

/-- Two agents, each with its own internal state space, observing the *same* environment. -/
def par (δ₁ : S → I → S) (δ₂ : S' → I → S') : S × S' → I → S × S' :=
  fun p i => (δ₁ p.1 i, δ₂ p.2 i)




/-! ### Coarse-graining and simulation -/




/-! ### Functoriality in the stimulus alphabet -/

/-- Re-encoding the environment: the agent reacts to `i'` as it would to `g i'`. -/
def relabel (δ : S → I → S) (g : I' → I) : S → I' → S := fun s i' => δ s (g i')



/-! ### Order rigidity: monotone agents -/

section Monotone

variable [LinearOrder S] [OrderBot S] [OrderTop S]





end Monotone

end Doppelganger


