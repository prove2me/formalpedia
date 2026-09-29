-- Prove2me | solution 1 for CompressionOWF.inverter_failure_infinite
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:15:59.558179+00:00
-- url     : https://prove2.me/submissions/0f73678e-50da-458c-a7f8-60c8e34efcc3

-- Sol generated from Speculative/AutoResearch/CompressionNonuniform.lean
import Mathlib
import Definitions.Def_Speculative_AutoResearch_CompressionNonuniform
import Definitions.Def_Speculative_AutoResearch_CompressionOneWayFunctions
import Definitions.Def_Speculative_AutoResearch_CompressionSearchToDecision
/-
Copyright (c) 2025. All rights reserved.

# Failure Sets are Infinite: Non-Uniform Patching and Compression

## Overview

Fourth cycle of the Phase-B/M8 investigation.  Cycle 1
(`Shared.CompressionOneWayFunctions`) produced, for each algorithm of a class,
*one* string with a short description that the algorithm fails to output
(`owf_description_gap`).  The adversarial review raised the obvious objection: a
single failure could be an artefact, since an algorithm failing on finitely many
inputs can be repaired with a lookup table.

Here we prove that the objection cannot be sustained as soon as the collection
of algorithms is closed under exactly that repair operation:

* `PatchClosed` — closure of a set of algorithms under overwriting on a finite
  set of inputs (finite advice / a lookup table);
* `inverter_failure_infinite` — if no algorithm of a patch-closed collection
  inverts `f`, then *every* algorithm of the collection fails on an **infinite**
  set of inputs;
* `compression_failure_infinite` — hence every candidate compressor fails to
  output shortest programs on an infinite set of inputs, each of which
  nevertheless *has* a description.

To rule out vacuity we exhibit a concrete patch-closed collection
(`tailAvoiding`, the algorithms that agree with the "delete the first bit"
map only finitely often) containing the function `tagTrue` of cycle 1 and
containing no inverter for it (`tagTrue_hard_tailAvoiding`), so the hypotheses
are simultaneously satisfiable and the conclusion has real content
(`tagTrue_failures_infinite`).

**Open point recorded for the next cycle.**  Patch closure and the strong
`search_mem` axiom of `SearchClosedClass` pull in opposite directions: search
closure forces the class to control the length of outputs uniformly in the guard
parameter, whereas finite patching destroys any uniform length control.  Whether
a single class can satisfy both *and* contain a one-way function is Conjecture 6
of `FUTURE_DIRECTIONS.md`.

No axioms beyond the standard three, no `sorry`.
-/

open CompressionOWF




/-! ## A concrete patch-closed collection with a non-invertible function -/







open CompressionOWF in
theorem solution{Comp : Set (Str → Str)} (hpatch : PatchClosed Comp)
    (f : Str → Str) (hhard : ∀ A ∈ Comp, ¬ Inverts f A) (A : Str → Str) (hA : A ∈ Comp) :
    {y : Str | Describable f y ∧ f (A y) ≠ y}.Infinite := by
  classical
  by_contra hcon
  rw [Set.not_infinite] at hcon
  set F : Finset Str := hcon.toFinset with hF
  have hchoice : ∀ y : Str, ∃ x : Str, Describable f y → f x = y := by
    intro y
    by_cases h : Describable f y
    · exact ⟨h.choose, fun _ => h.choose_spec⟩
    · exact ⟨[], fun hh => absurd hh h⟩
  choose g hg using hchoice
  refine hhard (fun y => if y ∈ F then g y else A y) (hpatch A hA F g) ?_
  intro y hy
  by_cases hmem : y ∈ F
  · simp only [if_pos hmem]
    exact hg y hy
  · simp only [if_neg hmem]
    have hnot : y ∉ {y : Str | Describable f y ∧ f (A y) ≠ y} := by
      intro hy'
      exact hmem (by rw [hF, Set.Finite.mem_toFinset]; exact hy')
    by_contra hne
    exact hnot ⟨hy, hne⟩
