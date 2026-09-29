-- Prove2me | Definitions.Def_Probability_MinorModel
-- name    : Probability_MinorModel
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:09.241868+00:00
-- url     : https://prove2.me/theorems/2d1e2b95-3e37-4a24-8943-ebace5f41d58
-- title:
--   Aether Catalog definitions — Probability_MinorModel
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.MinorModel`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/MinorModel.lean by skeleton subtraction
import Mathlib
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

namespace MinorTheory.MinorModel

open SimpleGraph

variable {V W : Type*}

/-- A **branch-set model** witnessing that `H` is a minor of `G`: pairwise
disjoint, non-empty, connected branch sets `branch w ⊆ V`, one per vertex `w` of
`H`, with every edge of `H` realised by a `G`-edge between branch sets. -/
structure IsMinorModel (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set of each `H`-vertex. -/
  branch : W → Set V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_disjoint : ∀ ⦃w w'⦄, w ≠ w' → Disjoint (branch w) (branch w')
  branch_connected : ∀ w, (G.induce (branch w)).Connected
  edge_lift : ∀ ⦃a b⦄, H.Adj a b → ∃ x ∈ branch a, ∃ y ∈ branch b, G.Adj x y

/-- `H` is a **minor** of `G` when a branch-set model exists. -/
def IsMinor (H : SimpleGraph W) (G : SimpleGraph V) : Prop :=
  Nonempty (IsMinorModel H G)

/-
Reflexivity: every graph is a minor of itself, via singleton branch sets.
-/

/-
A subgraph is a minor: if `G ≤ G'` (same vertex set) then `G` is a minor of
`G'`.  Hence the subgraph order refines the minor order.
-/

end MinorTheory.MinorModel


