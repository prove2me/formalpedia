-- Prove2me | solution 1 for Doppelganger.dense_lockSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:48:09.75618+00:00
-- url     : https://prove2.me/submissions/33edce2c-20bd-4ce2-91ac-b5c69b7c75ec

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
omit [DiscreteTopology I] in
theorem solution(δ : S → I → S) (h : PhaseLocking δ) : Dense (LockSet δ) := by
  obtain ⟨w, hw⟩ := h
  rw [dense_iff_inter_open]
  intro U hU hne
  obtain ⟨x, hx⟩ := hne
  obtain ⟨F, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x hx
  set N := (F.sup id) + 1 with hN
  refine ⟨splice x N w (x 0), hsub ?_, ⟨N + w.length, ?_⟩⟩
  · intro a ha
    have hlt : a < N := by
      have hle : a ≤ F.sup id := Finset.le_sup (f := id) (by simpa using ha)
      omega
    simp only [splice, if_pos hlt]
    exact (hu a (by simpa using ha)).2
  · rw [pre_splice]
    exact hw.append_left δ (pre x N)
