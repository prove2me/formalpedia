-- Prove2me | Theorems.Thm_Doppelganger_cerny3_rotation_stream_not_mem_lockSet
-- name    : Doppelganger.cerny3_rotation_stream_not_mem_lockSet
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-15T00:48:14.354682+00:00
-- url     : https://prove2.me/theorems/e58f5b98-7462-4c0e-bb66-793a7107aa34
-- title:
--   Along the constant "rotate" stimulus stream the two Černý doppelgängers never
-- statement:
--   Along the constant "rotate" stimulus stream the two Černý doppelgängers never
--   synchronize: every prefix acts by a bijection of the state space.
--
--   ```lean
--   theorem Doppelganger.cerny3_rotation_stream_not_mem_lockSet:
--       (fun _ : ℕ => (0 : Fin 2)) ∉ LockSet cerny3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/DoppelgangerPhaseLock/Sharpness.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/DoppelgangerPhaseLock/Sharpness.lean#L30

-- Thm stub generated from Applications/DoppelgangerPhaseLock/Sharpness.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Decidability
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
/-
# Doppelgänger Phase-Lock — sharpness of the topological zero–one law

Adversarial review of `Applications.DoppelgangerPhaseLock.Topology`: the zero–one law says
the set of synchronizing stimulus streams is either empty or open and dense.  Could it be
*everything* — i.e. is a phase-locking agent guaranteed to lock along **every** stream?
And is `LockSet` perhaps even clopen, so that the dichotomy is a triviality?

Both are false, and this file proves it with an explicit witness.  For the three-state
Černý agent the constant "rotate forever" stimulus stream never locks the doppelgängers,
because the rotation stimulus acts bijectively and bijections never destroy the distinction
between two states.  Hence for that agent `LockSet` is open, dense, **not** closed and
**not** the whole space: the zero–one law of `Topology.lean` is exactly as strong as it can
be, and no stronger.

## Main results

* `Doppelganger.cerny3_rotation_stream_not_mem_lockSet` — a non-locking stream for a
  phase-locking agent.
* `Doppelganger.not_isClosed_lockSet_cerny3` — the lock set is not closed.
* `Doppelganger.lockSet_cerny3_sharp` — open + dense + neither closed nor everything.
* `Doppelganger.cerny3_not_contractive` — the same agent admits no contractive metric, so
  the analytic mechanism of `Contraction.lean` is strictly stronger than phase-lock itself.
-/

open Doppelganger

theorem Doppelganger.cerny3_rotation_stream_not_mem_lockSet:
    (fun _ : ℕ => (0 : Fin 2)) ∉ LockSet cerny3 := by sorry
