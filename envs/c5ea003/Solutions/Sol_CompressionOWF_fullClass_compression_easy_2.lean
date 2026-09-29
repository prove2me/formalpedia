-- Prove2me | solution 2 for CompressionOWF.fullClass_compression_easy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T09:49:43.414398+00:00
-- url     : https://prove2.me/submissions/4f9467ce-6e9a-4444-95b8-93cd8ff9e2fd

import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
open CompressionOWF in
theorem solution :
    ∀ f ∈ fullClass.Comp, HonestIn fullClass f → ∃ A ∈ fullClass.Comp, ShortestFinder f A := by
  have hshort : ∀ (f : Str → Str) (y : Str), Describable f y →
      ∃ p : Str, p.length = K f y ∧ f p = y := by
    intro f y hy
    obtain ⟨p₀, hp₀⟩ := hy
    exact Nat.sInf_mem (s := {n | ∃ p : Str, p.length = n ∧ f p = y}) ⟨p₀.length, p₀, rfl, hp₀⟩
  intro f _ _
  classical
  refine ⟨fun y => if h : Describable f y then Classical.choose (hshort f y h) else [],
    Set.mem_univ _, ?_⟩
  intro y hy
  have hs := Classical.choose_spec (hshort f y hy)
  simp only [dif_pos hy]
  exact ⟨hs.2, hs.1⟩
