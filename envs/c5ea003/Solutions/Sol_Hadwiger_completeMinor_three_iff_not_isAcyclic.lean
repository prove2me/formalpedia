-- Prove2me | solution 1 for Hadwiger.completeMinor_three_iff_not_isAcyclic
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:38:07.330902+00:00
-- url     : https://prove2.me/submissions/ff73b206-a828-4220-b006-42581a18e568

-- Sol generated from Probability/HadwigerForest.lean
import Mathlib
import Definitions.Def_Probability_ForestDensity
import Definitions.Def_Probability_HadwigerK3
import Theorems.Thm_Hadwiger_completeMinor_three_of_not_isAcyclic
import Theorems.Thm_Hadwiger_not_isAcyclic_of_completeMinor_three
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






open Hadwiger in
theorem solution: CompleteMinor 3 G ↔ ¬ G.IsAcyclic :=
  ⟨not_isAcyclic_of_completeMinor_three, completeMinor_three_of_not_isAcyclic⟩
