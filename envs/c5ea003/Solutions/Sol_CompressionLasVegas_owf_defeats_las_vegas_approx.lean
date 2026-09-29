-- Prove2me | solution 1 for CompressionLasVegas.owf_defeats_las_vegas_approx
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-09-21T01:44:35.840242+00:00
-- url     : https://prove2.me/submissions/ef60f148-d372-4c8e-a2d8-032d50300db8

import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionLasVegasOWF
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions

set_option maxHeartbeats 1000000 in
open scoped Classical in
open CompressionLasVegas CompressionOWF in
theorem solution (C : LasVegasClass) (f : Str → Str)
    (hf : OneWayIn C.toSearchClosedClass f) (A : Str → Str → Str)
    (hA : ∀ r : Str, A r ∈ C.Comp) (R : List Str) (g : ℕ → ℕ) :
    ¬ SeededApproxFinder f A R g := by
  -- ==== the one-way-function lemma, proved from the definitions ====
  have owf_defeats_las_vegas : ∀ (C : LasVegasClass) (f : Str → Str),
      OneWayIn C.toSearchClosedClass f → ∀ (A : Str → Str → Str),
      (∀ r : Str, A r ∈ C.Comp) → ∀ (R : List Str),
      ∃ y : Str, Describable f y ∧ ∀ r ∈ R, f (A r y) ≠ y := by
    intro C f hf A hA R
    classical
    obtain ⟨hfC, hhon, hinv⟩ := hf
    have hmem : tryList f A R ∈ C.Comp := C.tryList_mem f hfC A hA R
    have hnot := hinv _ hmem
    rw [Inverts] at hnot
    push_neg at hnot
    obtain ⟨y, hy, hne⟩ := hnot
    refine ⟨y, hy, ?_⟩
    intro r hr heq
    rcases hfind : R.find? (fun r => decide (f (A r y) = y)) with _ | r'
    · have hnone := (List.find?_eq_none).mp hfind r hr
      simp only [decide_eq_true_eq] at hnone
      exact hnone heq
    · refine hne ?_
      have hsome := List.find?_some hfind
      simp only [decide_eq_true_eq] at hsome
      show f (tryList f A R y) = y
      unfold tryList
      rw [hfind]
      exact hsome
  -- ==== end of inlined lemma ====
  intro hfind
  -- the proved theorem supplies a describable `y` that no seed inverts
  obtain ⟨y, hy, hne⟩ := owf_defeats_las_vegas C f hf A hA R
  obtain ⟨r, hr, heq, -⟩ := hfind y hy
  exact hne r hr heq
