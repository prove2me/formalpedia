-- Prove2me | solution 1 for Doppelganger.cerny3_rotation_stream_not_mem_lockSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-15T00:50:12.831574+00:00
-- url     : https://prove2.me/submissions/6dc0d6d8-8131-4ea1-bab7-645d5c3b27fd

-- Sol generated from Applications/DoppelgangerPhaseLock/Sharpness.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Decidability
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
import Theorems.Thm_Doppelganger_getElem_pre
import Theorems.Thm_Doppelganger_injective_drive_of_forall_mem
import Theorems.Thm_Doppelganger_length_pre
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





/-! ### The analytic mechanism is strictly stronger than the phenomenon -/




open Doppelganger in
theorem solution:
    (fun _ : ℕ => (0 : Fin 2)) ∉ LockSet cerny3 := by
  rintro ⟨n, hn⟩
  have hpre : pre (fun _ : ℕ => (0 : Fin 2)) n = List.replicate n 0 := by
    apply List.ext_getElem <;> simp
  rw [hpre] at hn
  have hinj : Function.Injective (drive cerny3 (List.replicate n 0)) := by
    refine injective_drive_of_forall_mem (fun i hi => ?_)
    have hi0 : i = 0 := by simpa using List.eq_of_mem_replicate hi
    subst hi0
    intro a b hab
    simpa [cerny3] using hab
  have hcontra := hinj (hn 0 1)
  simp at hcontra
