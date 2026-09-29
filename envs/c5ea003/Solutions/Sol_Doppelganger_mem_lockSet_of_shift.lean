-- Prove2me | solution 1 for Doppelganger.mem_lockSet_of_shift
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-18T15:12:52.28798+00:00
-- url     : https://prove2.me/submissions/e0e189b6-b86d-4dd5-ad88-fa9253882b91

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
open Doppelganger in
theorem solution {S I : Type*} (δ : S → I → S) (x : ℕ → I)
    (h : (fun k => x (k + 1)) ∈ LockSet δ) : x ∈ LockSet δ := by
  obtain ⟨n, hn⟩ := h
  -- one extra leading symbol: feed it first, then the locking word of the shifted stream
  refine ⟨n + 1, fun s t => ?_⟩
  have hpre : pre x (n + 1) = x 0 :: pre (fun k => x (k + 1)) n := by
    simp [pre, List.ofFn_succ]
  rw [hpre]
  simp only [drive, List.foldl_cons]
  exact hn (δ s (x 0)) (δ t (x 0))
