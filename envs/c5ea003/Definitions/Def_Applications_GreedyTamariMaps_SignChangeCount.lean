-- Prove2me | Definitions.Def_Applications_GreedyTamariMaps_SignChangeCount
-- name    : Applications_GreedyTamariMaps_SignChangeCount
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:46:45.888269+00:00
-- url     : https://prove2.me/theorems/52042785-4e46-40e4-8021-3abe351d5236
-- title:
--   Aether Catalog definitions — Applications_GreedyTamariMaps_SignChangeCount
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.GreedyTamariMaps.SignChangeCount`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/GreedyTamariMaps/SignChangeCount.lean by skeleton subtraction
import Mathlib
/-
# Abstract sign-change counting on two-letter words

This file isolates the *domain-general* combinatorial kernel underlying the peak/valley
identity used on the greedy-Tamari side of the conjectured bijection (see
`DyckValleys.lean`).  Over an arbitrary two-letter alphabet — here modelled by `Bool`
(`true` = "rise", `false` = "fall") — the number of `rise→fall` descents and the number of
`fall→rise` ascents of a word differ by a **pure boundary term** depending only on the first
and last letters.

This is a genuinely general statement: it makes no positivity or balance assumption (unlike
Dyck words), and specialises, on words that begin with a rise and end with a fall, to
"there is exactly one more descent than ascent".

## Main results

* `Applications.GreedyTamariMaps.SignChange.descents_sub_ascents`: for any nonempty
  `Bool`-word, `#descents − #ascents = w(head) − w(last)` (as integers), where `w true = 1`,
  `w false = 0`.
* `Applications.GreedyTamariMaps.SignChange.descents_eq_ascents_succ`: a `Bool`-word that
  starts with `true` and ends with `false` has `#descents = #ascents + 1`.
* `Applications.GreedyTamariMaps.SignChange.descents_eq_ascents_of_closed`: a `Bool`-word
  that starts and ends with the *same* letter has `#descents = #ascents`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The peak/valley identity is a shadow of an alphabet-independent
  fact: on any two-letter word, descents minus ascents is a boundary invariant.  Surprising
  angle: the interior of the word is irrelevant — only the first and last letters matter.
Experiment (Experimenter): Checked on `Bool`-words up to length 5 that
  `#descents − #ascents` equals `w(head) − w(last)` and, for words starting `true` ending
  `false`, that `#descents = #ascents + 1` (mirroring the Dyck computation in
  `ComputationalEvidence.md`).
Analysis (Analyst): The naive statement (descents = ascents + 1) is not closed under taking
  tails; the *signed boundary invariant* is the induction-closed strengthening, proved by a
  two-step list induction with a four-way case split on the two leading letters.
Critique (Critic): No result is vacuous.  `descents_sub_ascents` is a genuine induction
  (`omega` closes each of the four leading-letter cases, not `rfl`/`decide`).  The two
  corollaries are non-vacuous specialisations; the `closed` case needs both endpoints equal,
  and is false for open words, so the hypothesis is load-bearing.
Synthesis (PI): This is the reusable, alphabet-agnostic backbone that the Dyck-specific
  `peaks_eq_valleys_succ` instantiates; it is stated over `Bool` so any future two-letter
  encoding (e.g. black/white boundary letters of bipartite maps) can reuse it directly.
-/

namespace Applications.GreedyTamariMaps.SignChange

/-- Number of **descents** (`true` immediately followed by `false`) in a `Bool`-word. -/
def descents : List Bool → ℕ
  | true :: false :: t => 1 + descents (false :: t)
  | _ :: t => descents t
  | [] => 0

/-- Number of **ascents** (`false` immediately followed by `true`) in a `Bool`-word. -/
def ascents : List Bool → ℕ
  | false :: true :: t => 1 + ascents (true :: t)
  | _ :: t => ascents t
  | [] => 0

/-- Boundary weight `w true = 1`, `w false = 0`. -/
def wt : Bool → ℤ
  | true => 1
  | false => 0

/-
**Signed boundary invariant.**  For any nonempty `Bool`-word,
`#descents − #ascents = w(head) − w(last)`.
-/

/-
A `Bool`-word that begins with a rise and ends with a fall has exactly one more descent
than ascent.
-/

/-
A `Bool`-word whose first and last letters agree has equally many descents and
ascents.
-/

end Applications.GreedyTamariMaps.SignChange


