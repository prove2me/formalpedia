-- Prove2me | Theorems.Thm_Doppelganger_injective_drive_of_forall_mem
-- name    : Doppelganger.injective_drive_of_forall_mem
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:38:21.415186+00:00
-- url     : https://prove2.me/theorems/b856ffec-ee24-4767-8817-573884e1c501
-- title:
--   If every stimulus *occurring in `w`* acts injectively, then `w` acts injectively.
-- statement:
--   If every stimulus *occurring in `w`* acts injectively, then `w` acts injectively.
--
--   ```lean
--   theorem Doppelganger.injective_drive_of_forall_mem{δ : S → I → S} {w : List I}
--       (h : ∀ i ∈ w, Function.Injective (δ · i)) : Function.Injective (drive δ w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Boundary.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Boundary.lean#L33

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Boundary.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Boundary
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

open Doppelganger

variable {S I : Type*}

/-! ### Reversible agents never phase-lock -/

theorem Doppelganger.injective_drive_of_forall_mem{δ : S → I → S} {w : List I}
    (h : ∀ i ∈ w, Function.Injective (δ · i)) : Function.Injective (drive δ w) := by sorry
