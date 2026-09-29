-- Prove2me | solution 1 for MinorTheory.MinorModel.isMinor_of_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:49:30.264041+00:00
-- url     : https://prove2.me/submissions/d701b2ef-51f4-40eb-b70c-969aa7569ef3

-- Sol generated from Probability/MinorModel.lean
import Mathlib
import Definitions.Def_Probability_MinorModel
import Definitions.Def_Probability_OrderFramework
/-
  The Graph-Minor Relation via Branch-Set Models
  ==============================================

  `OrderFramework.lean` developed minor-closed classes over an abstract order;
  `ForestDensity.lean` used the subgraph specialisation.  This file pins down the
  genuine **graph-minor relation** itself, via the classical *branch decomposition*
  (model) definition: `H` is a minor of `G` when one can choose pairwise-disjoint,
  non-empty, connected *branch sets* of `G`-vertices, one per vertex of `H`, so
  that every edge of `H` is witnessed by a `G`-edge between the corresponding
  branch sets.

  Main results:

  * `isMinor_refl`    : every graph is a minor of itself (reflexivity).
  * `isMinor_of_le`   : a subgraph is a minor (the subgraph order refines the
                        minor order), justifying the specialisation used in
                        `ForestDensity.lean`.

  Together with `OrderFramework.excl_minorClosed` this gives the concrete meaning
  of "excluding `H` as a minor".

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): the branch-set model is the right computable handle
    on the minor relation; reflexivity and "subgraph ⇒ minor" should both follow
    from the *singleton* branch decomposition `w ↦ {w}`.
  Experiment (Experimenter): defined `IsMinorModel` as a structure (branch map +
    nonemptiness + disjointness + connectivity + edge-lifting) and `IsMinor` as
    its inhabitation.  Singleton branch sets discharge reflexivity; the only
    subtlety is connectivity of a one-vertex induced subgraph.
  Analysis (Analyst): connectivity of `G.induce {w}` is exactly
    `IsTree.of_subsingleton` (the subtype `↥{w}` is nonempty + subsingleton) — a
    pleasant reuse of the tree API also driving the density bound.
  Critique (Critic): transitivity of the minor relation (composing branch
    decompositions, which requires routing `H`-edges through `G`-paths) is the
    genuinely hard structural law; it is deliberately *not* claimed here and is
    listed as the next milestone in FUTURE_DIRECTIONS.md.
  Synthesis (PI): reflexivity + subgraph-refinement ground the abstract order in
    the concrete minor relation named in the mission title.
  -- !-- Lab Notes -- !--
-/

open MinorTheory.MinorModel

open SimpleGraph

variable {V W : Type*}



/-
Reflexivity: every graph is a minor of itself, via singleton branch sets.
-/

/-
A subgraph is a minor: if `G ≤ G'` (same vertex set) then `G` is a minor of
`G'`.  Hence the subgraph order refines the minor order.
-/


open MinorTheory.MinorModel in
theorem solution{G G' : SimpleGraph V} (h : G ≤ G') : IsMinor G G' := by
  refine' ⟨ fun w => { w }, _, _, _, _ ⟩ <;> simp +decide
  exact fun a b hab => h hab
