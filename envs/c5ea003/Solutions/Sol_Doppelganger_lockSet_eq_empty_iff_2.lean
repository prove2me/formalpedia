-- Prove2me | solution 2 for Doppelganger.lockSet_eq_empty_iff
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-18T06:36:18.970972+00:00
-- url     : https://prove2.me/submissions/1109685c-5621-4306-ba2d-1f1e9d043ab9

import Mathlib
import Definitions.Def_Applications_DoppelgangerPhaseLock_Core
import Definitions.Def_Applications_DoppelgangerPhaseLock_Topology

open Doppelganger

variable {S I : Type*}

theorem solution [Nonempty I] (δ : S → I → S) :
    LockSet δ = ∅ ↔ ¬ PhaseLocking δ := by
  constructor
  · intro hempty ⟨w, hw⟩
    inhabit I
    let x : ℕ → I := fun k => if h : k < w.length then w[k] else default
    have hpre : pre x w.length = w := by
      apply List.ext_getElem
      · simp [pre]
      · intro n h₁ h₂
        have hn : n < w.length := by simpa [pre] using h₁
        simp [pre, x, hn]
    have hx : x ∈ LockSet δ := ⟨w.length, by simpa [hpre] using hw⟩
    rw [hempty] at hx
    exact False.elim hx
  · intro hpl
    ext x
    refine ⟨?_, False.elim⟩
    intro hx
    obtain ⟨n, hn⟩ := hx
    exact hpl ⟨pre x n, hn⟩
