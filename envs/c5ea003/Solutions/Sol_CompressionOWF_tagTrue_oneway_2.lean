-- Prove2me | solution 2 for CompressionOWF.tagTrue_oneway
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:32:17.639858+00:00
-- url     : https://prove2.me/submissions/e1e86b9c-3856-4755-b998-255b4aaa9b6c

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution : OneWayIn lengthClass tagTrue := by
  refine ⟨?_, ⟨fun n => n, trivial, ?_⟩, ?_⟩
  · show ∀ p : Str, p.length ≤ (tagTrue p).length
    intro p
    simp [tagTrue]
  · rintro y ⟨p, rfl⟩
    have h : K tagTrue (tagTrue p) ≤ p.length := Nat.sInf_le ⟨p, rfl, rfl⟩
    show K tagTrue (tagTrue p) ≤ (tagTrue p).length
    exact h.trans (by simp [tagTrue])
  · intro A hA hinv
    have h1 : tagTrue (A [true]) = [true] := hinv [true] ⟨[], rfl⟩
    have h2 : [true].length ≤ (A [true]).length := hA [true]
    simp only [tagTrue, List.cons.injEq, true_and] at h1
    rw [h1] at h2
    simp at h2
