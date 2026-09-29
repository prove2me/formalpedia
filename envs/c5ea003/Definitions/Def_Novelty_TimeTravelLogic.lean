-- Prove2me | Definitions.Def_Novelty_TimeTravelLogic
-- name    : Novelty_TimeTravelLogic
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T11:43:42.493975+00:00
-- url     : https://prove2.me/theorems/2d65a377-e65d-40fb-ad70-c46f81735cb8
-- title:
--   Aether Catalog definitions — Novelty_TimeTravelLogic
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.TimeTravelLogic`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/TimeTravelLogic.lean by skeleton subtraction
import Mathlib

/-!
# A small mathematics of causal loops and branching timelines

This file deliberately separates three notions which informal discussions often conflate:
periodicity, pointwise self-consistency, and existence of a fixed point.  For a deterministic
causal update `step`, a closed causal history is a periodic point.  Novikov consistency says
that every state visited by that history is unchanged by `step`.

The central result is a collapse theorem: if the causal update is idempotent, every nonempty
closed history collapses to a fixed point.  Idempotence is essential; Boolean negation gives a
closed history of every even length but has no fixed point.  This same example yields a precise
formal grandfather-paradox no-go theorem.

Finally, histories represented by finite lists give a minimal branching-timeline model.  A
traveller's intervention appends a new event, creating a strict descendant rather than changing
its ancestor.  Strict descent is irreflexive, so this construction cannot create a causal loop.
-/

namespace TimeTravel

/-- A deterministic causal law maps the present event-state to its causal successor. -/
abbrev CausalLaw (α : Type*) := α → α

/-- A state closes after `period` causal steps. -/
def ClosedOrbit {α : Type*} (step : CausalLaw α) (period : ℕ) (start : α) : Prop :=
  step^[period] start = start

/-- Every event-state encountered before closure is itself stable under the causal law. -/
def NovikovConsistent {α : Type*} (step : CausalLaw α) (period : ℕ) (start : α) : Prop :=
  ∀ k < period, step (step^[k] start) = step^[k] start

/-- The loop contains a fixed point among the states it visits. -/
def LoopHasFixedPoint {α : Type*} (step : CausalLaw α) (period : ℕ) (start : α) : Prop :=
  ∃ k < period, step (step^[k] start) = step^[k] start





/-- A causal law is idempotent when applying it twice has the same effect as once. -/
def Idempotent {α : Type*} (step : CausalLaw α) : Prop := ∀ x, step (step x) = step x




section Grandfather

/-- The minimal grandfather intervention flips whether the ancestor survives. -/
def grandfatherStep : Bool → Bool := fun alive => !alive







end Grandfather

section Branching

/-- A timeline is its finite sequence of events. Different continuations of one history are
literally different list values. -/
abbrev Timeline (Event : Type*) := List Event

/-- Time travel does not overwrite the source history: it creates a child branch. -/
def travel {Event : Type*} (source : Timeline Event) (intervention : Event) : Timeline Event :=
  source ++ [intervention]

/-- `ancestor a b` means that `a` is an initial segment of `b`. -/
def Ancestor {Event : Type*} (a b : Timeline Event) : Prop := a <+: b

/-- Proper causal descent is prefix descent together with inequality. -/
def StrictDescendant {Event : Type*} (child parent : Timeline Event) : Prop :=
  Ancestor parent child ∧ parent ≠ child









end Branching

end TimeTravel


