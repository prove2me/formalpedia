-- Prove2me | solution 1 for Hadwiger.isMinor_of_isMinor_induce
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:38:09.104094+00:00
-- url     : https://prove2.me/submissions/cac18cac-5f1f-4b86-a288-3b07f69f37bf

-- Sol generated from Probability/HadwigerCore.lean
import Mathlib
import Definitions.Def_Probability_HadwigerCore
import Definitions.Def_Probability_MinorModel
import Definitions.Def_Probability_OrderFramework
import Theorems.Thm_Hadwiger_walkMinor_iff_isMinor
/-
  The Graph-Minor Preorder: Composition of Branch-Set Models
  ==========================================================

  `MinorModel.lean` defined the graph-minor relation `IsMinor H G` through
  branch-set models and proved reflexivity plus "subgraph ⇒ minor"; its Lab
  Notes explicitly flagged **transitivity** — composing branch decompositions —
  as "the genuinely hard structural law … deliberately not claimed here".
  This file closes that gap, and in doing so builds the walk-level API for
  induced connectivity that the rest of the Hadwiger development rests on.

  Main results:

  * `Hadwiger.SetConnected`               : walk-based connectivity of a vertex
                                            set, with
    `Hadwiger.setConnected_iff_induce_connected` identifying it with
    `(G.induce S).Connected`.
  * `Hadwiger.walkMinor_iff_isMinor`      : the walk-based model is equivalent
                                            to the catalog's `IsMinorModel`.
  * `Hadwiger.setConnected_biUnion`       : a union of connected branch sets
                                            indexed by a connected set, glued by
                                            lifted edges, is connected.
  * `Hadwiger.isMinor_trans`              : **transitivity of the minor
                                            relation** — the graph-minor
                                            relation is a preorder.
  * `Hadwiger.isMinor_of_le_of_isMinor`,
    `Hadwiger.isMinor_mono_left`          : interaction with the subgraph order.

  -- !-- Lab Notes -- !--
  Hypothesis (Hypothesizer): transitivity of the branch-set minor relation is
    provable by *composition*: the branch set of `w` in the bottom graph is the
    union of the middle-graph branch sets over the middle-graph branch set of
    `w`.  The only hard point is connectivity of that union.
  Experiment (Experimenter): the subtype-valued `(G.induce S).Connected` is
    awkward for gluing, so we first introduced the walk-level predicate
    `SetConnected` (every two members joined by a walk staying inside `S`) and
    proved it equivalent to the induced-subgraph formulation using Mathlib's
    `Walk.induce` / `Walk.map_induce`.
  Analysis (Analyst): with `SetConnected` in hand the gluing lemma is a clean
    induction along a walk of the middle graph: each step `x → y` inside the
    branch set is realised by a lifted edge between `c x` and `c y`, and the two
    endpoints are joined inside `c x` resp. `c y` by connectivity.
  Critique (Critic): disjointness of the composed branch sets needs the *middle*
    disjointness only through "different indices ⇒ disjoint bottom sets", which
    is exactly where injectivity of a branch decomposition hides; the proof is
    recorded in `composeModel` and uses no extra hypotheses.
  Synthesis (PI): `IsMinor` is now known to be a genuine preorder, so
    `MinorClosed` classes in the abstract `OrderFramework` may legitimately be
    read as minor-closed classes of graphs.
  -- !-- Lab Notes -- !--
-/

open Hadwiger

open SimpleGraph

variable {U V W : Type*} {G : SimpleGraph V}

/-! ### Walk-level connectivity of a vertex set -/








/-! ### Walk-based minor models -/





/-! ### Gluing connected sets along a walk -/



/-! ### Transitivity -/



/-! ### Passing between a graph and its induced subgraphs -/

/-- Connectivity inside an induced subgraph pushes forward to the ambient
graph. -/
theorem setConnected_image_val {S : Set V} {T : Set S}
    (h : SetConnected (G.induce S) T) : SetConnected G (Subtype.val '' T) := by
  obtain ⟨⟨a, ha⟩, hconn⟩ := h
  refine ⟨⟨a.1, ⟨a, ha, rfl⟩⟩, ?_⟩
  rintro x ⟨b, hb, rfl⟩ y ⟨c, hc, rfl⟩
  obtain ⟨p, hp⟩ := hconn hb hc
  refine ⟨p.map (Embedding.induce S).toHom, ?_⟩
  intro z hz
  have hz' : z ∈ p.support.map (Embedding.induce S).toHom :=
    SimpleGraph.Walk.support_map (Embedding.induce S).toHom p ▸ hz
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hz'
  exact ⟨w, hp w hw, rfl⟩


/-! ### Interaction with the subgraph order -/





open Hadwiger in
theorem solution{H : SimpleGraph W} {S : Set V}
    (h : MinorTheory.MinorModel.IsMinor H (G.induce S)) :
    MinorTheory.MinorModel.IsMinor H G := by
  obtain ⟨M⟩ := walkMinor_iff_isMinor.mpr h
  refine walkMinor_iff_isMinor.mp
    ⟨⟨fun w => Subtype.val '' M.branch w, ?_, ?_, ?_, ?_⟩⟩
  · intro w
    obtain ⟨a, ha⟩ := M.branch_nonempty w
    exact ⟨a.1, ⟨a, ha, rfl⟩⟩
  · intro w w' hww'
    exact Set.disjoint_image_of_injective Subtype.val_injective (M.branch_disjoint hww')
  · intro w
    exact setConnected_image_val (M.branch_connected w)
  · intro a b hab
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge_lift hab
    exact ⟨x.1, ⟨x, hx, rfl⟩, y.1, ⟨y, hy, rfl⟩, hxy⟩
