-- Prove2me | Theorems.Thm_Doppelganger_Locks_append_left
-- name    : Doppelganger.Locks.append_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:36:44.957692+00:00
-- url     : https://prove2.me/theorems/cb9e7929-a0e1-4c7b-968a-5e15e4805435
-- title:
--   Extra stimuli *before* a locking word cannot prevent the lock.
-- statement:
--   Extra stimuli *before* a locking word cannot prevent the lock.
--
--   ```lean
--   theorem Doppelganger.Locks.append_left(δ : S → I → S) {w : List I} (h : Locks δ w) (u : List I) :
--       Locks δ (u ++ w) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Core.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Core.lean#L101

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Core.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
/-
# Doppelgänger Phase-Lock — Core theory

Two spatially separated but *identical* agents are modelled as two copies of one
deterministic reactive system

```
δ : S → I → S
```

(`S` = internal state space, `I` = alphabet of environmental stimuli).  Both
copies observe the *same* stimulus stream; the question of "quantum telepathic
synchronization" is thereby demystified into an exact mathematical question:

> for which `δ` does there exist a finite stimulus word `w` after which the two
> copies occupy the *same* internal state, no matter how far apart their initial
> states were?

This is exactly the classical notion of a **synchronizing (reset) word** for a
deterministic automaton, and this file develops it from scratch in the language
of phase-locking agents.

## Main definitions

* `Doppelganger.drive δ w s` — the state reached from `s` after the stimulus word `w`.
* `Doppelganger.Locks δ w` — `w` *phase-locks* the pair of agents: it maps **all**
  states to a common state.
* `Doppelganger.Mergeable δ s t` — the particular pair `(s,t)` can be locked.
* `Doppelganger.PhaseLocking δ` — some word locks the doppelgänger pair.

## Main results

* `Doppelganger.drive_append`, `Doppelganger.transitionHom` — the stimulus monoid acts
  on the state space; `w ↦ drive δ w` is a monoid *anti*-homomorphism
  `FreeMonoid I →* (Function.End S)ᵐᵒᵖ` (algebraic layer).
* `Doppelganger.locks_ideal` — the set of phase-locking words is a two-sided ideal of
  the free monoid of stimuli: *once telepathy is possible, no amount of extra noise,
  before or after, can destroy it*.
* `Doppelganger.Locks.flatten_of_mem` — a stimulus stream chopped into blocks locks as
  soon as **one** block locks (used for the quantitative rarity estimates).
* `Doppelganger.phaseLocking_iff_const_mem_range` — phase-locking is equivalent to the
  transition monoid containing a constant map (rank-one element).
* `Doppelganger.locked_forever` — phase-lock is absorbing: the diagonal is invariant.
-/

open Doppelganger

variable {S I : Type*}

/-! ### The stimulus action -/








/-! ### Phase-locking -/

theorem Doppelganger.Locks.append_left(δ : S → I → S) {w : List I} (h : Locks δ w) (u : List I) :
    Locks δ (u ++ w) := by sorry
