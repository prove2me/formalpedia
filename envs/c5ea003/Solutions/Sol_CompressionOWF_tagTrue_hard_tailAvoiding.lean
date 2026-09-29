-- Prove2me | solution 1 for CompressionOWF.tagTrue_hard_tailAvoiding
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T06:16:02.061592+00:00
-- url     : https://prove2.me/submissions/d3d11963-8b31-42a7-bf2d-8056ede22aed

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
theorem solution: ∀ A ∈ tailAvoiding, ¬ Inverts tagTrue A := by
  intro A hA hinv
  have hall : ∀ p : Str, A (true :: p) = (true :: p).tail := by
    intro p
    have hdesc : Describable tagTrue (true :: p) := ⟨p, rfl⟩
    have h := hinv (true :: p) hdesc
    simp only [tagTrue, List.cons.injEq] at h
    simpa using h.2
  have hinf : {y : Str | A y = y.tail}.Infinite :=
    Set.infinite_of_injective_forall_mem
      (f := fun p : Str => true :: p) (by intro a b h; simpa using h) hall
  exact hinf hA
