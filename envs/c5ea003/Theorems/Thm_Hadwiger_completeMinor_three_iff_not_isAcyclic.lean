-- Prove2me | Theorems.Thm_Hadwiger_completeMinor_three_iff_not_isAcyclic
-- name    : Hadwiger.completeMinor_three_iff_not_isAcyclic
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:42:31.603313+00:00
-- url     : https://prove2.me/theorems/383838e9-0fef-43db-b396-968df477cedd
-- title:
--   Excluded-minor characterisation of forests.
-- statement:
--   **Excluded-minor characterisation of forests.**  `K₃` is a minor of `G` if
--   and only if `G` contains a cycle.
--
--   ```lean
--   theorem Hadwiger.completeMinor_three_iff_not_isAcyclic: CompleteMinor 3 G ↔ ¬ G.IsAcyclic := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/HadwigerForest.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/HadwigerForest.lean#L113

-- Thm stub generated from Probability/HadwigerForest.lean
import Mathlib
import Definitions.Def_Probability_ForestDensity
import Definitions.Def_Probability_HadwigerK3
/-
  Forests are Exactly the `K₃`-Minor-Free Graphs
  ==============================================

  `ForestDensity.lean` established that forests are closed under *subgraphs* and
  listed the full contraction-closed statement — "forests `=` the class
  excluding `K₃` as a **minor**" — as the natural next target.  This file proves
  it, in both directions and with no finiteness hypothesis:

  * `Hadwiger.not_isAcyclic_of_completeMinor_three` : a graph with a `K₃` minor
                                            contains a cycle.  (Equivalently:
                                            forests are `K₃`-minor-free, so the
                                            class of forests really is
                                            minor-closed, not merely
                                            subgraph-closed.)
  * `Hadwiger.completeMinor_three_iff_not_isAcyclic` : `K₃ ≼ G ↔ G` has a cycle.
  * `Hadwiger.acyclicClass_eq_excl_K3`      : the catalog's `acyclicClass` is
                                            exactly the excluded-`K₃` class.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): acyclicity should be *minor*-closed, not just
    subgraph-closed; the obstruction to a direct proof is that contraction is not
    a subgraph operation.
  Experiment (Experimenter): rather than tracking contractions, we contradict the
    bridge characterisation of acyclicity: given a `K₃` model with linking edges
    `x₀x₁`, `y₀y₂`, `z₁z₂`, the route
    `x₀ ⇝ y₀ → y₂ ⇝ z₂ → z₁ ⇝ x₁` travels inside the branch sets and never uses
    the edge `x₀x₁`, so `x₀x₁` is not a bridge.
  Analysis (Analyst): every edge of that route has both endpoints inside a single
    branch set, or joins branch `0` to branch `2`, or branch `1` to branch `2`;
    disjointness of the branch sets rules out each of them being `x₀x₁`.  This is
    the only place where disjointness of a minor model is used essentially.
  Critique (Critic): the statement needs no finiteness and no decidability — the
    walks come from the walk-level connectivity of `HadwigerCore.lean`, and
    `Walk.toDeleteEdges` transports them into the edge-deleted graph.
  Synthesis (PI): combined with `completeMinor_three_of_not_isAcyclic` this gives
    a clean excluded-minor characterisation of forests, closing the milestone
    named in `ForestDensity.lean`.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

theorem Hadwiger.completeMinor_three_iff_not_isAcyclic: CompleteMinor 3 G ↔ ¬ G.IsAcyclic := by sorry
