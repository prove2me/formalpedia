-- Prove2me | solution 1 for Doppelganger.isOpen_lockSet
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:56:47.067093+00:00
-- url     : https://prove2.me/submissions/abfb5f60-6881-4eac-9eca-ea4ca2189bbe

-- Sol generated from Applications/DoppelgangerPhaseLock/Topology.lean
import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
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




lemma pre_congr {x y : ℕ → I} {n : ℕ} (h : ∀ i < n, y i = x i) : pre y n = pre x n := by
  unfold pre
  congr 1
  funext i
  exact h i i.isLt




variable [TopologicalSpace I] [DiscreteTopology I]








open Doppelganger in
theorem solution(δ : S → I → S) : IsOpen (LockSet δ) := by
  rw [isOpen_iff_forall_mem_open]
  rintro x ⟨n, hn⟩
  refine ⟨⋂ i ∈ Finset.range n, (fun y : ℕ → I => y i) ⁻¹' {x i}, ?_, ?_, ?_⟩
  · intro y hy
    simp only [Set.mem_iInter, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_range] at hy
    exact ⟨n, by rw [pre_congr (fun i hi => hy i hi)]; exact hn⟩
  · exact isOpen_biInter_finset (fun i _ => (isOpen_discrete _).preimage (continuous_apply i))
  · simp
