-- Prove2me | Theorems.Thm_CompressionOWF_tagTrue_hard_tailAvoiding
-- name    : CompressionOWF.tagTrue_hard_tailAvoiding
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-13T04:40:18.027022+00:00
-- url     : https://prove2.me/theorems/21f30f71-86ac-4044-8fd2-9d564845e86d
-- title:
--   No algorithm of `tailAvoiding` inverts `tagTrue`: an inverter must delete the
-- statement:
--   No algorithm of `tailAvoiding` inverts `tagTrue`: an inverter must delete the
--   leading bit on the whole (infinite) range of `tagTrue`.
--
--   ```lean
--   theorem CompressionOWF.tagTrue_hard_tailAvoiding: ∀ A ∈ tailAvoiding, ¬ Inverts tagTrue A := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Speculative/AutoResearch/CompressionNonuniform.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Speculative/AutoResearch/CompressionNonuniform.lean#L119

-- Thm stub generated from Speculative/AutoResearch/CompressionNonuniform.lean
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

theorem CompressionOWF.tagTrue_hard_tailAvoiding: ∀ A ∈ tailAvoiding, ¬ Inverts tagTrue A := by sorry
