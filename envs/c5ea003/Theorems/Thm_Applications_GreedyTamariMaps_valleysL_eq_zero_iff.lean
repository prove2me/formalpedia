-- Prove2me | Theorems.Thm_Applications_GreedyTamariMaps_valleysL_eq_zero_iff
-- name    : Applications.GreedyTamariMaps.valleysL_eq_zero_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:20:06.603526+00:00
-- url     : https://prove2.me/theorems/004ba981-895b-4a1b-8a1d-97d4cfd26dc1
-- title:
--   ValleysL eq zero iff
-- statement:
--   Formal statement of `Applications.GreedyTamariMaps.valleysL_eq_zero_iff` from the Aether Catalog (Applications). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Applications.GreedyTamariMaps.valleysL_eq_zero_iff(l : List DyckStep) :
--       valleysL l = 0 ↔
--         l = List.replicate (l.count U) U ++ List.replicate (l.count D) D := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/GreedyTamariMaps/DyckValleys.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/GreedyTamariMaps/DyckValleys.lean#L152

-- Thm stub generated from Applications/GreedyTamariMaps/DyckValleys.lean
import Mathlib
import Definitions.Def_Applications_GreedyTamariMaps_DyckValleys
/-
# Valleys and peaks of Dyck words (the greedy-Tamari lower-endpoint statistic)

This file studies the **valley statistic** on Dyck words, which is the combinatorial
statistic recording, for an interval `[x, y]` of a Tamari-type order on Dyck paths, the
number of valleys of the *lower endpoint* `x`.  A **valley** of a Dyck path is a factor
`DU` (a down step immediately followed by an up step); a **peak** is a factor `UD`.

We build on Mathlib's `DyckWord` (`Mathlib.Combinatorics.Enumerative.DyckWord`), reusing in
particular `DyckWord.head_eq_U`, `DyckWord.getLast_eq_D` and, in the companion file, the
enumeration `DyckWord.card_dyckWord_semilength_eq_catalan`.

## Main results

* `Applications.GreedyTamariMaps.peaksL_sub_valleysL`: the load-bearing invariant.  For any
  nonempty list of Dyck steps, `#peaks − #valleys = φ(head) − φ(last)` (as integers), where
  `φ U = 1` and `φ D = 0`.  Proved by a genuine two-step list induction.
* `Applications.GreedyTamariMaps.peaks_eq_valleys_succ`: for every nonempty Dyck word,
  `#peaks = #valleys + 1`.  This is the classical "peaks are one more than valleys" identity,
  here derived from the invariant together with `head_eq_U`/`getLast_eq_D`.
* `Applications.GreedyTamariMaps.valleys_le_semilength`: the valley count is bounded by the
  semilength (needed to organise the refined enumeration).
* `Applications.GreedyTamariMaps.refined_valley_enumeration`: the refined valley counts of
  Dyck words of semilength `n` sum over `k` to `catalan n` — the aggregate consistency the
  conjectured refinement must satisfy on the greedy-Tamari side.
* `Applications.GreedyTamariMaps.valleys_eq_zero_iff`: a Dyck word of semilength `n` has no
  valley iff it is exactly the minimal path `Uⁿ Dⁿ`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): On the greedy-Tamari side of the conjectured bijection the
  refining statistic is the valley count of the lower endpoint.  A robust, purely local
  identity should govern valleys: for every nonempty Dyck path `#peaks = #valleys + 1`.
  Surprising corollary tested: this needs *only* that the path starts with `U` and ends
  with `D`; the balance/positivity conditions are not used.
Experiment (Experimenter): Enumerated all Dyck paths of semilength ≤ 5 as `List Bool`,
  computed the valley distribution (Narayana rows `1`; `1,1`; `1,3,1`; `1,6,6,1`;
  `1,10,20,10,1`) and verified `peaks = valleys + 1` on every path.  See
  `ComputationalEvidence.md`.
Analysis (Analyst): The clean inductive invariant is the *signed* identity
  `peaks − valleys = φ(head) − φ(last)` with `φ U = 1`, `φ D = 0`; it holds for *all*
  lists of two-letter steps and specialises to `peaks = valleys + 1` once `head = U`,
  `last = D`.  The naive statement `peaks = valleys + 1` is NOT closed under taking tails,
  which is why the signed invariant (closed under peeling the head) is the right induction.
Critique (Critic): No result here is vacuous.  `peaks_eq_valleys_succ` is a real
  arithmetic consequence of a genuine induction (`rcases` on the two leading steps +
  `omega`), not `rfl`/`decide`.  The hypothesis `p ≠ 0` is load-bearing: the empty word
  has `peaks = valleys = 0`, so the `+1` fails there.
Synthesis (PI): `peaks_eq_valleys_succ` and `valleys_le_semilength` are the reusable
  substrate for the refined enumeration (companion file) and for any future formal
  bijection with bipartite planar maps.
-/

open Applications.GreedyTamariMaps

open DyckStep List






/-
**Signed peak/valley invariant.**  For any nonempty list of Dyck steps,
`#peaks − #valleys = φ(head) − φ(last)`.  This is the induction-friendly form of the
classical "one more peak than valley" identity.
-/

/-
**Peaks are one more than valleys.**  For every nonempty Dyck word,
`#peaks = #valleys + 1`.
-/

/-
The valley count of a list of Dyck steps is at most the number of `U` steps.
-/

/-
The valley count of a Dyck word is bounded by its semilength.
-/


/-
**Aggregate consistency of the refined valley enumeration.**  Summing the refined
valley counts over all valley numbers `k ∈ {0, …, n}` recovers the total number of Dyck
words of semilength `n`, namely `catalan n` (Mathlib's
`DyckWord.card_dyckWord_semilength_eq_catalan`).  This is the identity any correct
refinement of the greedy-Tamari lower endpoints by valley count must satisfy.
-/

/-
A list of Dyck steps has no valley (`D` followed by `U`) iff every `U` precedes every
`D`, i.e. it is `Uᵃ Dᵇ` with `a = #U` and `b = #D`.
-/

theorem Applications.GreedyTamariMaps.valleysL_eq_zero_iff(l : List DyckStep) :
    valleysL l = 0 ↔
      l = List.replicate (l.count U) U ++ List.replicate (l.count D) D := by sorry
