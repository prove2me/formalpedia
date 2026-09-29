-- Prove2me | Definitions.Def_Probability_ForestDensity
-- name    : Probability_ForestDensity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:09.366435+00:00
-- url     : https://prove2.me/theorems/403a96df-f122-4197-929d-583795474371
-- title:
--   Aether Catalog definitions — Probability_ForestDensity
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.ForestDensity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/ForestDensity.lean by skeleton subtraction
import Mathlib
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

namespace MinorTheory.ForestDensity

open SimpleGraph

variable {V : Type*}

/-- The class of acyclic graphs (forests) on a fixed vertex set `V`. -/
def acyclicClass (V : Type*) : Set (SimpleGraph V) := {G | G.IsAcyclic}


/-- Edge density of a finite graph: `|E| / |V|` as a rational number.  When
`V` is empty this evaluates to `0`. -/
noncomputable def edgeDensity (G : SimpleGraph V) : ℚ :=
  (Nat.card G.edgeSet : ℚ) / (Nat.card V : ℚ)

/-
**Forest edge bound.** A non-empty finite forest on `V` has at most
`|V| - 1` edges, i.e. `|E| + 1 ≤ |V|`.
-/

/-
Every finite tree has edge density strictly below `1`.
-/

/-
**Forests are below the 3/2 threshold.** Every finite forest has edge density
strictly below `3/2`.
-/


end MinorTheory.ForestDensity


