-- Prove2me | Theorems.Thm_SimpleGraph_IsStarSum_card_le_seven_mul_indepNum
-- name    : SimpleGraph.IsStarSum.card_le_seven_mul_indepNum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:32:55.249062+00:00
-- url     : https://prove2.me/theorems/c6b12010-a473-43cd-be19-46d3f1dc09d1
-- title:
--   The `1/7` barrier, integral form.
-- statement:
--   **The `1/7` barrier, integral form.**  If every side of a star amalgam has at least two
--   vertices and carries an independent set of relative density at least `1/4`, then
--   `n ≤ 7 α(G)`.  Compare `SimpleGraph.IsStarSum.indepRatio_ge_of_sides`, whose bound
--   `1/4 - (m-1)(3/4)/n` becomes vacuous for many parts: the absolute floor `1/7` survives.
--
--   ```lean
--   theorem SimpleGraph.IsStarSum.card_le_seven_mul_indepNum[Nonempty ι] [∀ i, DecidablePred (· ∈ A i)]
--       {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
--       (hdens : ∀ i, (Finset.univ.filter (· ∈ A i)).card ≤ 4 * (s i).card)
--       (hside : ∀ i, 2 ≤ (Finset.univ.filter (· ∈ A i)).card)
--       (hcover : Fintype.card V + (Fintype.card ι - 1)
--         = ∑ i, (Finset.univ.filter (· ∈ A i)).card) :
--       Fintype.card V ≤ 7 * G.indepNum := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/StarAmalgamSeventhBarrier.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/StarAmalgamSeventhBarrier.lean#L94

-- Thm stub generated from Novelty/StarAmalgamSeventhBarrier.lean
import Mathlib
import Definitions.Def_Novelty_IndependenceRatioChromatic
import Definitions.Def_Novelty_OneSumEqualityAnalysis
import Definitions.Def_Novelty_OneSumStarAmalgam
import Definitions.Def_Novelty_StarAmalgamThresholdFamily

/-!
# The `1/7` barrier for star amalgams of threshold graphs

`Novelty.OneSumIndepRatioCounterexample` showed that the threshold property `i(G) ≥ 1/4` is
**not** closed under vertex amalgamation, and `Novelty.StarAmalgamThresholdFamily` produced an
`m`-parameter family of amalgams of `K₈ - e` whose independence ratio is `(m+1)/(7m+1)`, which
decreases to `1/7`.  This file closes the gap from the other side: **`1/7` is a genuine floor.**

Main results.

* `SimpleGraph.IsStarSum.card_le_seven_mul_indepNum` — if every side of a star amalgam carries
  an independent set of relative density at least `1/4` (and every side contains a vertex other
  than the cut vertex), then `n ≤ 7 α(G)`.
* `SimpleGraph.IsStarSum.indepRatio_ge_seventh` — the rational form `i(G) ≥ 1/7`.
* `SimpleGraph.StarFamily.seventh_barrier_optimal` — the constant `1/7` cannot be improved:
  the family `StarK8 m` satisfies the hypotheses for every `m ≥ 1`, and its ratio comes
  arbitrarily close to `1/7`.

The proof is a two-regime argument.  Write `Nᵢ` for the size of the `i`-th side, `sᵢ` for the
witnessing independent set (`Nᵢ ≤ 4|sᵢ|`), and `m` for the number of parts.

* *Large sides* (`Nᵢ ≥ 8` for all `i`): the plain defect bound `∑|sᵢ| ≤ α + (m-1)` already
  suffices, because `n = ∑Nᵢ - (m-1) ≥ 7m + 1` leaves enough room.
* *Some small side* (`N_j ≤ 7`): the defect bound is far too lossy there (it can even be
  vacuous), so one switches to the *cut-free* union bound `∑|tᵢ| ≤ α`, where `tᵢ` is `sᵢ`
  with the cut vertex deleted — replaced by an arbitrary non-cut vertex of the side when that
  deletion empties it.  The pointwise estimate `Nᵢ ≤ 7|tᵢ| + 1` holds for every `i` (it is
  `Nᵢ ≤ 4|sᵢ| ≤ 4|tᵢ| + 4 ≤ 7|tᵢ| + 1`, using `|tᵢ| ≥ 1`), and the small side gives the one
  extra unit `N_j ≤ 7|t_j|` that upgrades `7α ≥ n - 1` to `7α ≥ n`.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): iterating 1-sums of graphs of independence ratio `1/4` cannot push
the ratio below `1/7`, and `1/7` is exactly the infimum.
Experiment (Experimenter): the naive route -- feed `r = 1/4` into
`SimpleGraph.IsStarSum.indepRatio_ge_of_sides` -- yields `1/4 - (m-1)(3/4)/n`, which is
*negative* for `m` large relative to `n`, so it does not prove any absolute floor.  Numerically,
minimising `∑ max(αᵢ-1,1) / (∑(Nᵢ-1)+1)` subject to `αᵢ ≥ Nᵢ/4` over side sizes
`Nᵢ ∈ {2,...,20}` gives per-side ratios `(Nᵢ-4)/(4(Nᵢ-1))` for `Nᵢ ≥ 8` and `1/(Nᵢ-1)` for
`Nᵢ ≤ 7`; the minimum over both regimes is attained at `Nᵢ = 8`, value `1/7`.  Sample values:
`N = 8 → 1/7 ≈ 0.1429`, `N = 12 → 8/44 ≈ 0.1818`, `N = 7 → 1/6 ≈ 0.1667`,
`N = 4 → 1/3`, `N = 2 → 1`.  Two regimes therefore have to be combined, which is exactly the
case split of the formal proof.
Analysis (Analyst): the failure of the single-bound approach is structural, not technical: the
defect bound `∑|sᵢ| ≤ α + (m-1)` charges `m-1` copies of the cut vertex, and for small sides
that charge exceeds the entire side.  Deleting the cut vertex up front (the `tᵢ` construction)
makes the charge disappear, at the cost of one vertex per side -- affordable precisely when a
side is small.
Critique (Critic): the hypothesis `2 ≤ Nᵢ` is load-bearing.  Without it a side may equal `{v}`,
so `tᵢ = ∅`, and the small-side upgrade `N_j ≤ 7|t_j|` fails.  It is also not merely technical:
the statement is about amalgams in which every part genuinely contributes.
Synthesis (PI): the pair (`indepRatio_ge_seventh`, `exists_indepRatio_lt`) pins the exact
constant `1/7` for the closure of the `1/4`-threshold under vertex amalgamation.
-- !-- end Lab Notes -- !--
-/

open Finset

open SimpleGraph

variable {V ι : Type*} {G : SimpleGraph V} {H : ι → SimpleGraph V} {A : ι → Set V} {v : V}

open IsStarSum

variable (h : IsStarSum G H A v)
include h

variable [Fintype V] [DecidableEq V] [Fintype ι] [DecidableEq ι]

theorem SimpleGraph.IsStarSum.card_le_seven_mul_indepNum[Nonempty ι] [∀ i, DecidablePred (· ∈ A i)]
    {s : ι → Finset V} (hs : ∀ i, ↑(s i) ⊆ A i) (hi : ∀ i, (H i).IsIndepSet ↑(s i))
    (hdens : ∀ i, (Finset.univ.filter (· ∈ A i)).card ≤ 4 * (s i).card)
    (hside : ∀ i, 2 ≤ (Finset.univ.filter (· ∈ A i)).card)
    (hcover : Fintype.card V + (Fintype.card ι - 1)
      = ∑ i, (Finset.univ.filter (· ∈ A i)).card) :
    Fintype.card V ≤ 7 * G.indepNum := by sorry
