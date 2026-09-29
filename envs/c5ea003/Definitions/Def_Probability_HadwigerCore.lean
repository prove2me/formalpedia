-- Prove2me | Definitions.Def_Probability_HadwigerCore
-- name    : Probability_HadwigerCore
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:45.009326+00:00
-- url     : https://prove2.me/theorems/9186da9b-971d-4ac5-98e0-d78079da56c2
-- title:
--   Aether Catalog definitions — Probability_HadwigerCore
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.HadwigerCore`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/HadwigerCore.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Probability_MinorModel
import Definitions.Def_Probability_OrderFramework
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

namespace Hadwiger

open SimpleGraph

variable {U V W : Type*} {G : SimpleGraph V}

/-! ### Walk-level connectivity of a vertex set -/

/-- `SetConnected G S`: `S` is non-empty and any two of its members are joined by
a `G`-walk all of whose vertices lie in `S`. -/
def SetConnected (G : SimpleGraph V) (S : Set V) : Prop :=
  S.Nonempty ∧ ∀ ⦃x⦄, x ∈ S → ∀ ⦃y⦄, y ∈ S → ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S

theorem SetConnected.nonempty {S : Set V} (h : SetConnected G S) : S.Nonempty := h.1

theorem SetConnected.walk {S : Set V} (h : SetConnected G S) {x y : V} (hx : x ∈ S)
    (hy : y ∈ S) : ∃ p : G.Walk x y, ∀ z ∈ p.support, z ∈ S := h.2 hx hy


/-- The walk-level and induced-subgraph notions of connectivity agree. -/
theorem setConnected_iff_induce_connected {S : Set V} :
    SetConnected G S ↔ (G.induce S).Connected := by
  constructor
  · rintro ⟨⟨v, hv⟩, hconn⟩
    have hne : Nonempty S := ⟨⟨v, hv⟩⟩
    rw [connected_iff]
    refine ⟨?_, hne⟩
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨p, hp⟩ := hconn hx hy
    exact ⟨p.induce S hp⟩
  · intro hc
    obtain ⟨v⟩ := hc.nonempty
    refine ⟨⟨v.1, v.2⟩, ?_⟩
    intro x hx y hy
    obtain ⟨p⟩ := hc.preconnected ⟨x, hx⟩ ⟨y, hy⟩
    refine ⟨p.map (Embedding.induce S).toHom, ?_⟩
    intro z hz
    have hz' : z ∈ p.support.map (Embedding.induce S).toHom :=
      SimpleGraph.Walk.support_map (Embedding.induce S).toHom p ▸ hz
    obtain ⟨w, -, rfl⟩ := List.mem_map.mp hz'
    exact w.2



/-! ### Walk-based minor models -/

/-- A branch-set model of `H` inside `G`, with connectivity phrased at walk
level.  Equivalent to `MinorTheory.MinorModel.IsMinorModel` (see
`walkMinor_iff_isMinor`), but far more convenient for constructions. -/
structure WalkMinorModel (H : SimpleGraph W) (G : SimpleGraph V) where
  /-- The branch set attached to a vertex of `H`. -/
  branch : W → Set V
  branch_nonempty : ∀ w, (branch w).Nonempty
  branch_disjoint : ∀ ⦃w w'⦄, w ≠ w' → Disjoint (branch w) (branch w')
  branch_connected : ∀ w, SetConnected G (branch w)
  edge_lift : ∀ ⦃a b⦄, H.Adj a b → ∃ x ∈ branch a, ∃ y ∈ branch b, G.Adj x y

/-- Turn a walk-level model into a catalog model. -/
def WalkMinorModel.toMinorModel {H : SimpleGraph W} (M : WalkMinorModel H G) :
    MinorTheory.MinorModel.IsMinorModel H G where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_disjoint := M.branch_disjoint
  branch_connected w := setConnected_iff_induce_connected.mp (M.branch_connected w)
  edge_lift := M.edge_lift

/-- Turn a catalog model into a walk-level model. -/
def _root_.MinorTheory.MinorModel.IsMinorModel.toWalkModel {H : SimpleGraph W}
    (M : MinorTheory.MinorModel.IsMinorModel H G) : WalkMinorModel H G where
  branch := M.branch
  branch_nonempty := M.branch_nonempty
  branch_disjoint := M.branch_disjoint
  branch_connected w := setConnected_iff_induce_connected.mpr (M.branch_connected w)
  edge_lift := M.edge_lift


/-! ### Gluing connected sets along a walk -/

/-- **Gluing lemma.**  Let `c : V → Set U` assign to every vertex of `G` a
`K`-connected set, so that adjacent vertices of `G` have their sets joined by a
`K`-edge.  Then along any `G`-walk from `x` to `y` one can travel inside the
union of the sets attached to the walk's support. -/
theorem exists_walk_biUnion_of_walk {K : SimpleGraph U} {c : V → Set U}
    (hconn : ∀ v, SetConnected K (c v))
    (hlift : ∀ ⦃x y⦄, G.Adj x y → ∃ u ∈ c x, ∃ v ∈ c y, K.Adj u v)
    {x y : V} (p : G.Walk x y) :
    ∀ {u u' : U}, u ∈ c x → u' ∈ c y →
      ∃ q : K.Walk u u', ∀ z ∈ q.support, ∃ v ∈ p.support, z ∈ c v := by
  induction p with
  | @nil a =>
    intro u u' hu hu'
    obtain ⟨q, hq⟩ := (hconn a).walk hu hu'
    exact ⟨q, fun z hz => ⟨a, by simp, hq z hz⟩⟩
  | @cons a b d hab p ih =>
    intro u u' hu hu'
    obtain ⟨s, hs, t, ht, hst⟩ := hlift hab
    obtain ⟨q₁, hq₁⟩ := (hconn a).walk hu hs
    obtain ⟨q₂, hq₂⟩ := ih ht hu'
    refine ⟨q₁.append (Walk.cons hst q₂), ?_⟩
    intro z hz
    simp only [Walk.support_append, Walk.support_cons, List.tail_cons, List.mem_append] at hz
    rcases hz with h | h
    · exact ⟨a, by simp, hq₁ z h⟩
    · obtain ⟨v, hv, hzv⟩ := hq₂ z h
      exact ⟨v, by simp [hv], hzv⟩

/-- A union of connected sets indexed by a connected set, glued by lifted edges,
is connected. -/
theorem setConnected_biUnion {K : SimpleGraph U} {c : V → Set U} {S : Set V}
    (hS : SetConnected G S) (hconn : ∀ v, SetConnected K (c v))
    (hlift : ∀ ⦃x y⦄, G.Adj x y → ∃ u ∈ c x, ∃ v ∈ c y, K.Adj u v) :
    SetConnected K (⋃ v ∈ S, c v) := by
  obtain ⟨x₀, hx₀⟩ := hS.nonempty
  obtain ⟨u₀, hu₀⟩ := (hconn x₀).nonempty
  refine ⟨⟨u₀, Set.mem_biUnion hx₀ hu₀⟩, ?_⟩
  intro u hu u' hu'
  simp only [Set.mem_iUnion, exists_prop] at hu hu'
  obtain ⟨x, hx, hux⟩ := hu
  obtain ⟨y, hy, hu'y⟩ := hu'
  obtain ⟨p, hp⟩ := hS.walk hx hy
  obtain ⟨q, hq⟩ := exists_walk_biUnion_of_walk hconn hlift p hux hu'y
  refine ⟨q, fun z hz => ?_⟩
  obtain ⟨v, hv, hzv⟩ := hq z hz
  exact Set.mem_biUnion (hp v hv) hzv

/-! ### Transitivity -/

/-- Composition of branch-set models: if `H` is a minor of `G` and `G` is a
minor of `K`, the branch sets compose. -/
def composeModel {H : SimpleGraph W} {K : SimpleGraph U}
    (M : WalkMinorModel H G) (N : WalkMinorModel G K) : WalkMinorModel H K where
  branch w := ⋃ v ∈ M.branch w, N.branch v
  branch_nonempty w := by
    obtain ⟨v, hv⟩ := M.branch_nonempty w
    obtain ⟨u, hu⟩ := N.branch_nonempty v
    exact ⟨u, Set.mem_biUnion hv hu⟩
  branch_disjoint := by
    intro w w' hww'
    rw [Set.disjoint_left]
    intro u hu hu'
    simp only [Set.mem_iUnion, exists_prop] at hu hu'
    obtain ⟨x, hx, hux⟩ := hu
    obtain ⟨y, hy, huy⟩ := hu'
    have hxy : x ≠ y := by
      rintro rfl
      exact (Set.disjoint_left.mp (M.branch_disjoint hww') hx) hy
    exact (Set.disjoint_left.mp (N.branch_disjoint hxy) hux) huy
  branch_connected w :=
    setConnected_biUnion (M.branch_connected w) N.branch_connected N.edge_lift
  edge_lift := by
    intro a b hab
    obtain ⟨x, hx, y, hy, hxy⟩ := M.edge_lift hab
    obtain ⟨u, hu, v, hv, huv⟩ := N.edge_lift hxy
    exact ⟨u, Set.mem_biUnion hx hu, v, Set.mem_biUnion hy hv, huv⟩


/-! ### Passing between a graph and its induced subgraphs -/



/-! ### Interaction with the subgraph order -/




end Hadwiger


