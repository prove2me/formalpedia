-- Prove2me | solution 1 for Doppelganger.lockSet_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:56:47.608437+00:00
-- url     : https://prove2.me/submissions/ccd09166-9393-4fe7-8b07-03f3952941f2

-- Sol generated from Applications/DoppelgangerPhaseLock/Topology.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
import Theorems.Thm_Doppelganger_Locks_append_left
import Theorems.Thm_Doppelganger_pre_splice
/-
# Doppelgänger Phase-Lock — the topology of locking stimulus streams

Real environments do not hand the agents a finite word; they hand them an infinite
stimulus stream `x : ℕ → I`.  Equip the stream space with the product topology of the
discrete stimulus alphabet (the Cantor topology).  The **lock set**

`LockSet δ = {x | some finite prefix of x phase-locks the two agents}`

is then a topological object, and this file determines its topological type exactly:

* it is always **open** — locking is a finitary, observable event: it is decided by a
  finite prefix, so it survives every sufficiently small perturbation of the stream;
* it is **dense** as soon as the agent is phase-locking at all — any experiment, no matter
  how it has been constrained on finitely many observations, can still be continued into a
  locking stream;
* consequently it is either **empty** (non-locking agent) or **open and dense**, with
  nowhere-dense complement: a topological zero–one law for doppelgänger telepathy.

## Main results

* `Doppelganger.isOpen_lockSet`
* `Doppelganger.dense_lockSet`
* `Doppelganger.lockSet_eq_empty_iff`
* `Doppelganger.lockSet_dichotomy` — the zero–one law.
* `Doppelganger.interior_compl_lockSet` — nowhere-density of the failure set.
-/

open Doppelganger

variable {S I : Type*}








variable [TopologicalSpace I] [DiscreteTopology I]








open Doppelganger in
omit [TopologicalSpace I] [DiscreteTopology I] in
theorem solution[Nonempty I] (δ : S → I → S) :
    LockSet δ = ∅ ↔ ¬ PhaseLocking δ := by
  constructor
  · intro hempty ⟨w, hw⟩
    have : splice (fun _ => Classical.arbitrary I) 0 w (Classical.arbitrary I) ∈ LockSet δ := by
      refine ⟨0 + w.length, ?_⟩
      rw [pre_splice]
      exact hw.append_left δ _
    rw [hempty] at this
    exact this
  · intro hno
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨n, hn⟩
    exact hno ⟨pre x n, hn⟩
