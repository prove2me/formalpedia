-- Prove2me | solution 1 for CompressionLasVegas.owf_defeats_las_vegas
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-17T21:47:12.312579+00:00
-- url     : https://prove2.me/submissions/254b31c3-7ae8-4be6-8b52-db96131ba569

import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
open CompressionOWF CompressionLasVegas in
theorem solution (C : LasVegasClass) (f : Str → Str)
    (hf : OneWayIn C.toSearchClosedClass f)
    (A : Str → Str → Str) (hA : ∀ r : Str, A r ∈ C.Comp) (R : List Str) :
    ∃ y : Str, Describable f y ∧ ∀ r ∈ R, f (A r y) ≠ y := by
  by_contra hcon
  push Not at hcon
  have hinv : Inverts f (tryList f A R) := by
    intro y hy
    obtain ⟨r0, hr0, hf0⟩ := hcon y hy
    unfold tryList
    cases hfind : R.find? (fun r => decide (f (A r y) = y)) with
    | none =>
      rw [List.find?_eq_none] at hfind
      exact absurd (by simpa using hf0) (hfind r0 hr0)
    | some r =>
      have := List.find?_some hfind
      simpa using this
  exact hf.2.2 _ (C.tryList_mem f hf.1 A hA R) hinv
