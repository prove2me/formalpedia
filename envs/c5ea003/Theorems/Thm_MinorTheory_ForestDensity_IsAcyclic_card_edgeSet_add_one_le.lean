-- Prove2me | Theorems.Thm_MinorTheory_ForestDensity_IsAcyclic_card_edgeSet_add_one_le
-- name    : MinorTheory.ForestDensity.IsAcyclic.card_edgeSet_add_one_le
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:39:57.465717+00:00
-- url     : https://prove2.me/theorems/b1cb692f-df10-453f-a39d-4a012a038b04
-- title:
--   Card edgeSet add one le
-- statement:
--   Formal statement of `MinorTheory.ForestDensity.IsAcyclic.card_edgeSet_add_one_le` from the Aether Catalog (Probability). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem MinorTheory.ForestDensity.IsAcyclic.card_edgeSet_add_one_le[Finite V] [Nonempty V]
--       {G : SimpleGraph V} (h : G.IsAcyclic) :
--       Nat.card G.edgeSet + 1 ≤ Nat.card V := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/ForestDensity.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/ForestDensity.lean#L67

-- Thm stub generated from Probability/ForestDensity.lean
import Mathlib
import Definitions.Def_Probability_ForestDensity
import Definitions.Def_Probability_OrderFramework
/-
  Forests: a Minor-Closed Class Strictly Below Density 3/2
  =======================================================

  This file instantiates the abstract framework of `OrderFramework.lean` with the
  concrete order on `SimpleGraph V` (the subgraph order, a sub-relation of the
  graph-minor order) and studies the class of **forests** (acyclic graphs).

  The mission concerns ⊆-minimal minor-closed classes whose limiting density is
  below `3/2`.  The class of forests is the prototypical such class: its limiting
  density is exactly `1 < 3/2`.  Here we prove, with full rigour:

  * `acyclicClass_minorClosed`        : forests form a minor-closed class
                                        (instance of `MinorTheory.MinorClosed`).
  * `IsAcyclic.card_edgeSet_add_one_le`: the forest edge bound `|E| + 1 ≤ |V|`.
  * `IsTree.edgeDensity_lt_one`        : every tree has edge density `< 1`.
  * `acyclic_edgeDensity_lt_threshold` : every forest has edge density `< 3/2`.
  * `acyclicClass_below_threshold`     : the whole forest class lies strictly
                                         below the `3/2` density threshold.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the forest class is a genuine, non-trivial instance
    of a minor-closed class living strictly below the 3/2 density threshold.
  Experiment (Experimenter): instantiated `MinorTheory.MinorClosed` at
    `SimpleGraph V` with `≤ = subgraph`; the closure law is exactly
    `SimpleGraph.IsAcyclic.anti`.  The density bound reduces to the forest edge
    inequality, obtained by extending any forest to a spanning tree of the
    complete graph (`Connected.exists_isTree_le_of_le_of_isAcyclic`).
  Analysis (Analyst): the edge bound `|E| ≤ |V| - 1` is what forces density `< 1`;
    `1 < 3/2` then gives the threshold.  The empty-graph corner case is handled by
    `Nat.card V = 0` making the density `0`.
  Critique (Critic): we use the *subgraph* specialisation of the minor order, for
    which the class is provably minor-closed via `IsAcyclic.anti`.  The full
    contraction-closed statement (forests `= excl {K₃}` as minors) is recorded in
    FUTURE_DIRECTIONS.md as the natural next target.
  Synthesis (PI): forests realise the framework — a minor-closed class strictly
    below 3/2 — and the density gap `1 < 3/2` is the quantitative heart.
  -- !-- Lab Notes -- !--
-/

open MinorTheory.ForestDensity

open SimpleGraph

variable {V : Type*}




/-
**Forest edge bound.** A non-empty finite forest on `V` has at most
`|V| - 1` edges, i.e. `|E| + 1 ≤ |V|`.
-/

theorem MinorTheory.ForestDensity.IsAcyclic.card_edgeSet_add_one_le[Finite V] [Nonempty V]
    {G : SimpleGraph V} (h : G.IsAcyclic) :
    Nat.card G.edgeSet + 1 ≤ Nat.card V := by sorry
