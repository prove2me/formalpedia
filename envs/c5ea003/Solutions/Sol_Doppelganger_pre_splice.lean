-- Prove2me | solution 1 for Doppelganger.pre_splice
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-19T01:24:06.099817+00:00
-- url     : https://prove2.me/submissions/36aa7d59-d465-44b4-95cd-17a1a8994a98

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology
open Doppelganger in
theorem solution {I : Type*} (x : ℕ → I) (N : ℕ) (w : List I) (c : I) :
    pre (splice x N w c) (N + w.length) = pre x N ++ w := by
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
