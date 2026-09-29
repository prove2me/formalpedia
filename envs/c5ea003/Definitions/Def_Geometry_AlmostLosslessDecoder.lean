-- Prove2me | Definitions.Def_Geometry_AlmostLosslessDecoder
-- name    : Geometry_AlmostLosslessDecoder
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T23:39:21.834728+00:00
-- url     : https://prove2.me/theorems/46f312d7-465d-4bae-a006-7fbaa44625ad
-- title:
--   Aether Catalog definitions — Geometry_AlmostLosslessDecoder
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.AlmostLosslessDecoder`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/AlmostLosslessDecoder.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Geometry_AlmostLosslessCore
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

namespace AlmostLossless

open Finset

/-! ## 1. The scanning decoder and its exact cost -/

variable {α : Type*} [DecidableEq α] {M : ℕ}

/-- One left-to-right pass over a candidate list: returns the sublist of matching
candidates together with the number of hash comparisons performed. -/
def scan (H : α → Fin M) (c : Fin M) : List α → List α × ℕ
  | [] => ([], 0)
  | y :: ys =>
      let r := scan H c ys
      (if H y = c then y :: r.1 else r.1, r.2 + 1)



/-- The decoder: `some y` if exactly one candidate matches, `none` otherwise
(the singleton test is the built-in checksum: ambiguity is always *detected*).
The second component is the number of hash comparisons performed. -/
def decode (L : List α) (H : α → Fin M) (c : Fin M) : Option α × ℕ :=
  (match (scan H c L).1 with
    | [y] => some y
    | _ => none,
   (scan H c L).2)



/-! ## 2. No silent corruption -/



/-! ## 3. When does the decoder succeed? -/

variable [Fintype α]

/-- The set of codebooks that confuse `x` with another typical string. -/
def failSet (S : Finset α) (x : α) (M : ℕ) : Finset (α → Fin M) :=
  univ.filter (fun H => ∃ y ∈ S.erase x, H y = H x)


/-! ## 4. The random-coding bound -/



/-- The set of codebooks on which the scheme decodes `x` correctly. -/
def goodSet (L : List α) (x : α) (M : ℕ) : Finset (α → Fin M) :=
  univ.filter (fun H => (decode L H (H x)).1 = some x)



/-! ## 5. Derandomisation: a single good codebook exists -/

/-- The typical strings that a *fixed* codebook `H` fails to distinguish. -/
def badStrings (S : Finset α) (H : α → Fin M) : Finset α :=
  S.filter (fun x => ∃ y ∈ S.erase x, H y = H x)


end AlmostLossless


