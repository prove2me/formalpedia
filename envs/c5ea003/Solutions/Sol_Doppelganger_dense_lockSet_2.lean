-- Prove2me | solution 2 for Doppelganger.dense_lockSet
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:19:23.782922+00:00
-- url     : https://prove2.me/submissions/0fd40d8f-175c-48b7-9bfc-87feff6cae68

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
open Doppelganger Filter Topology in
theorem solution {S I : Type*} [TopologicalSpace I] (δ : S → I → S) (h : PhaseLocking δ) :
    Dense (LockSet δ) := by
  obtain ⟨w, hw⟩ := h
  -- splicing a prefix onto a locking word keeps the prefix readable
  have hpre : ∀ (x : ℕ → I) (N : ℕ) (c : I),
      pre (splice x N w c) (N + w.length) = pre x N ++ w := by
    intro x N c
    apply List.ext_getElem
    · simp [pre]
    · intro i h1 h2
      simp only [pre, List.getElem_ofFn]
      by_cases hi : i < N
      · rw [List.getElem_append_left (by simpa using hi)]
        simp [splice, hi]
      · rw [List.getElem_append_right (by simp; omega)]
        have hlt : i - N < w.length := by simp [pre] at h1; omega
        simp [splice, hi, List.getElem?_eq_getElem hlt]
  -- any word ending in a locking word locks
  have hlock : ∀ u : List I, Locks δ (u ++ w) := by
    intro u s t
    simp only [drive, List.foldl_append]
    exact hw _ _
  intro x
  -- the splices `x|_N ++ w ++ …` lie in the lock set and converge to `x`
  have hmem : ∀ N, splice x N w (x 0) ∈ LockSet δ := fun N =>
    ⟨N + w.length, by rw [hpre]; exact hlock _⟩
  have htend : Tendsto (fun N => splice x N w (x 0)) atTop (𝓝 x) := by
    rw [tendsto_pi_nhds]
    intro k
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_gt_atTop k] with N hN
    simp [splice, hN]
  exact mem_closure_of_tendsto htend (Eventually.of_forall hmem)
