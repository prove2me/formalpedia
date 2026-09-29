-- Prove2me | solution 2 for AlmostLossless.decode_cost
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-17T13:08:49.067969+00:00
-- url     : https://prove2.me/submissions/c9d3995a-5086-4ae3-a3d9-0eb26edffe40

-- Sol generated from Geometry/AlmostLosslessDecoder.lean
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
import Definitions.Def_Geometry_AlmostLosslessDecoder
/-
# Almost-lossless compression: an explicit decoder, its cost, and its failure probability

Part of the research thread *Compression Beyond the Pigeonhole Bound*
(Phase B, Question 2: can random number generators help?).

The scheme.  Fix a *typical set* `S : Finset α` (the strings the source actually
produces with high probability), enumerated as a duplicate-free candidate list
`L`, and a codebook `H : α → Fin M` drawn uniformly at random.  The encoder sends
`H x` (`⌈log₂ M⌉` bits).  The decoder scans `L`, collects all `y` with
`H y = H x`, and

* outputs `some y` **only** when that list is a singleton, and
* outputs `none` otherwise.

Main results:

* `AlmostLossless.decode_cost` — the decoder performs **exactly `|L|`** hash
  comparisons (an exact complexity figure, not an asymptotic one).
* `AlmostLossless.decode_never_wrong` — *no silent corruption*: whenever the
  decoder outputs a string, that string is the transmitted one.  Errors are
  always reported as `none`.
* `AlmostLossless.decode_success_of_not_mem_failSet` — the decoder succeeds
  unless the codebook collides on the typical set.
* `AlmostLossless.failSet_prob_le` / `AlmostLossless.success_prob_ge` — the
  Shannon random-coding bound in exact counting form and in ℝ:
  `P[failure] ≤ (|S| - 1)/M`, hence `P[success] ≥ 1 - ε` as soon as
  `M ≥ (|S| - 1)/ε`.
* `AlmostLossless.exists_good_codebook` — derandomisation: some *fixed*
  codebook of size `M` fails on at most `|S|(|S|-1)/M` typical strings.
-/

open AlmostLossless

open Finset

/-! ## 1. The scanning decoder and its exact cost -/

variable {α : Type*} [DecidableEq α] {M : ℕ}



omit [DecidableEq α] in
/-- **Exact cost of one pass**: one hash comparison per candidate. -/
theorem scan_snd (H : α → Fin M) (c : Fin M) (L : List α) :
    (scan H c L).2 = L.length := by
  induction L with
  | nil => rfl
  | cons y ys ih => simp [scan, ih]




/-! ## 2. No silent corruption -/



/-! ## 3. When does the decoder succeed? -/




/-! ## 4. The random-coding bound -/






/-! ## 5. Derandomisation: a single good codebook exists -/




open AlmostLossless in
omit [DecidableEq α] in
theorem solution(L : List α) (H : α → Fin M) (c : Fin M) :
    (decode L H c).2 = L.length := by
  simp [decode, scan_snd]
