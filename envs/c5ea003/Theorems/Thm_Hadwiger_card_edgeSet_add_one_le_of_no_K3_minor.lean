-- Prove2me | Theorems.Thm_Hadwiger_card_edgeSet_add_one_le_of_no_K3_minor
-- name    : Hadwiger.card_edgeSet_add_one_le_of_no_K3_minor
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:40:00.04698+00:00
-- url     : https://prove2.me/theorems/f2f576e5-376e-4845-b328-651fc6ae7e05
-- title:
--   Extremal bound for the excluded minor `K₃`.
-- statement:
--   **Extremal bound for the excluded minor `K₃`.**  A non-empty finite graph
--   with no `K₃` minor has at most `|V| − 1` edges.
--
--   ```lean
--   theorem Hadwiger.card_edgeSet_add_one_le_of_no_K3_minor[Finite V] [Nonempty V]
--       (h : ¬ CompleteMinor 3 G) : Nat.card G.edgeSet + 1 ≤ Nat.card V := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerDensity.lean#L49

-- Thm stub generated from Probability/HadwigerDensity.lean
import Mathlib
import Definitions.Def_Probability_ForestDensity
import Definitions.Def_Probability_HadwigerK3
/-
  Excluded Minors and Edge Density: the Extremal Bound for `K₃`
  ============================================================

  Mader-type theorems bound the number of edges of a `K_{k+1}`-minor-free graph
  linearly in the number of vertices.  This file proves the case `k = 2` in the
  formal framework of the catalog, by combining the excluded-minor
  characterisation of forests (`HadwigerForest.lean`) with the forest edge bound
  of `ForestDensity.lean`.  The contrapositive is the interesting direction: a
  graph with at least as many edges as vertices *must* have a `K₃` minor.

  Main results:

  * `Hadwiger.card_edgeSet_add_one_le_of_no_K3_minor` : `|E| + 1 ≤ |V|` for a
    non-empty finite `K₃`-minor-free graph.
  * `Hadwiger.edgeDensity_lt_one_of_no_K3_minor`      : density `< 1`.
  * `Hadwiger.completeMinor_three_of_card_le_card_edgeSet` : the extremal
    (contrapositive) form — `|V| ≤ |E|` forces a `K₃` minor.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): excluding a complete minor should be an
    *edge-density* restriction, and for `K₃` the extremal function should be
    exactly `|V| − 1`, attained by trees.
  Experiment (Experimenter): the excluded-minor characterisation
    `completeMinor_three_iff_not_isAcyclic` converts the hypothesis "no `K₃`
    minor" into acyclicity, after which `IsAcyclic.card_edgeSet_add_one_le`
    applies verbatim; the density statement needs the empty-vertex corner case,
    where `Nat.card V = 0` makes the density `0`.
  Analysis (Analyst): the bound is sharp — every tree attains `|E| + 1 = |V|` —
    so the extremal function for `K₃` is exactly `n − 1`, and no further
    structural information about `K₃`-minor-free graphs is needed.  For `K₄` the
    same scheme would need the series-parallel edge bound `2n − 3`.
  Critique (Critic): the statement is not vacuous and does not hold with `|E|`
    replaced by `|E| + 2`: the path on three vertices has `|E| + 1 = |V|`.
  Synthesis (PI): the `k = 2` case of the Mader/Kostochka programme is now a
    theorem here, giving the density half of the excluded-minor picture that
    `ForestDensity.lean` only had for the subgraph order.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Hadwiger.card_edgeSet_add_one_le_of_no_K3_minor[Finite V] [Nonempty V]
    (h : ¬ CompleteMinor 3 G) : Nat.card G.edgeSet + 1 ≤ Nat.card V := by sorry
