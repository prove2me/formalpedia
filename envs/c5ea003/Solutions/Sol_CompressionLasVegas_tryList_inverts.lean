-- Prove2me | solution 1 for CompressionLasVegas.tryList_inverts
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:42:36.875953+00:00
-- url     : https://prove2.me/submissions/5fef1cb7-b83c-4aba-a674-c0646dc38cb6

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open CompressionOWF CompressionLasVegas in
theorem solution (f : Str → Str) (A : Str → Str → Str) (R : List Str)
    (h : ∀ y : Str, Describable f y → ∃ r ∈ R, f (A r y) = y) :
    Inverts f (tryList f A R) := by
  intro y hy
  obtain ⟨r0, hr0, hf0⟩ := h y hy
  unfold tryList
  cases hfind : R.find? (fun r => decide (f (A r y) = y)) with
  | none =>
    rw [List.find?_eq_none] at hfind
    exact absurd (by simpa using hf0) (hfind r0 hr0)
  | some r =>
    have := List.find?_some hfind
    simpa using this
