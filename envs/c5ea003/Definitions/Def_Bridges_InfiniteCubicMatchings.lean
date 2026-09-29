-- Prove2me | Definitions.Def_Bridges_InfiniteCubicMatchings
-- name    : Bridges_InfiniteCubicMatchings
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:24:39.899983+00:00
-- url     : https://prove2.me/theorems/299ffa16-bd7e-4557-a7bc-f3b1def51148
-- title:
--   Aether Catalog definitions — Bridges_InfiniteCubicMatchings
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.InfiniteCubicMatchings`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/InfiniteCubicMatchings.lean by skeleton subtraction
import Mathlib
/-
# Perfect matching conjectures in (possibly infinite) cubic bridgeless graphs

This file develops a formal framework, valid for **arbitrary** (finite or infinite) vertex
types, for the three classical perfect-matching conjectures on cubic bridgeless graphs:

* the **Berge–Fulkerson conjecture** (`BergeFulkerson`): six perfect matchings covering
  every edge exactly twice;
* the **Fan–Raspaud conjecture** (`FanRaspaud`): three perfect matchings with empty
  intersection;
* the **Máčajová–Škoviera conjecture** (`MacajovaSkoviera`): two perfect matchings whose
  intersection contains no odd edge cut.

The main results proved here are

* `PerfectMatching.exists_mem_cutEdges` and `PerfectMatching.card_inter_cutEdges_odd`:
  the *parity lemma* in the infinite setting — a perfect matching meets every edge cut with
  a **finite odd side** in an odd (in particular nonzero) number of edges;
* `BergeFulkerson.fanRaspaud` : BF ⟹ FR;
* `FanRaspaud.macajovaSkoviera` : FR ⟹ MŠ (this is where the parity lemma is used);
* `BergeFulkerson.macajovaSkoviera` : BF ⟹ MŠ;
* `not_bergeFulkerson_of_oddCut_singleton` and friends: all three conjectures **fail** for a
  graph possessing a one-edge cut with a finite odd side (the infinite analogue of "a cubic
  graph with a bridge has no such family"); hence bridgelessness is a necessary hypothesis;
* `ProperThreeEdgeColoring.bergeFulkerson` : a 3-edge-colourable graph satisfies BF (by
  doubling the colour classes) — this works verbatim for infinite graphs;
* transport of all three properties along graph isomorphisms.

Everything is stated for an arbitrary vertex type `V`; no finiteness of `V` is assumed
anywhere.
-/

namespace Bridges.InfiniteCubicMatchings

universe u v

variable {V : Type u} {G : SimpleGraph V}

/-! ## Perfect matchings as fixed-point-free involutions -/

/-- A perfect matching of `G`, encoded as a fixed-point-free involution `partner` of the
vertex set all of whose orbits are edges of `G`.  This is the standard encoding and works
for infinite graphs, where a matching cannot be described by a finite edge list. -/
structure PerfectMatching (G : SimpleGraph V) where
  /-- the vertex matched to a given vertex -/
  partner : V → V
  /-- a vertex is adjacent to its partner -/
  isAdj : ∀ v, G.Adj v (partner v)
  /-- the partner map is an involution -/
  invol : ∀ v, partner (partner v) = v

namespace PerfectMatching

/-- The set of edges of a perfect matching. -/
def edges (M : PerfectMatching G) : Set (Sym2 V) := {e | ∃ v, e = s(v, M.partner v)}





/-- The subgraph associated with a perfect matching. -/
def toSubgraph (M : PerfectMatching G) : G.Subgraph where
  verts := Set.univ
  Adj u w := G.Adj u w ∧ M.partner u = w
  adj_sub := fun h => h.1
  edge_vert := fun _ => Set.mem_univ _
  symm := by
    rintro u w ⟨h, rfl⟩
    exact ⟨h.symm, M.invol u⟩


end PerfectMatching

/-! ## Edge cuts with a finite side -/

/-- The edge cut determined by a finite set `S` of vertices: the edges of `G` with exactly
one endpoint in `S`. -/
def cutEdges (G : SimpleGraph V) (S : Finset V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ u w, e = s(u, w) ∧ u ∈ S ∧ w ∉ S}


/-- The edge cut of an arbitrary, possibly infinite, set of vertices. -/
def cutEdgesSet (G : SimpleGraph V) (S : Set V) : Set (Sym2 V) :=
  {e ∈ G.edgeSet | ∃ u w, e = s(u, w) ∧ u ∈ S ∧ w ∉ S}


/-- An *odd cut* (with a finite side): the cut of a finite vertex set of odd cardinality.
In an infinite graph, cuts both of whose sides are infinite carry no parity information,
so this finiteness restriction is essential. -/
def IsOddCut (G : SimpleGraph V) (C : Set (Sym2 V)) : Prop :=
  ∃ S : Finset V, Odd S.card ∧ C = cutEdges G S

/-! ## A combinatorial lemma: fixed-point-free involutions have even orbit sets -/


/-! ## The parity lemma -/

namespace PerfectMatching

variable (M : PerfectMatching G)





end PerfectMatching

/-! ## The three conjectures -/

/-- The Berge–Fulkerson property: there are six perfect matchings such that every edge
belongs to exactly two of them. -/
def BergeFulkerson (G : SimpleGraph V) : Prop :=
  ∃ M : Fin 6 → PerfectMatching G,
    ∀ e ∈ G.edgeSet, {i : Fin 6 | e ∈ (M i).edges}.ncard = 2

/-- The Fan–Raspaud property: there are three perfect matchings with empty intersection. -/
def FanRaspaud (G : SimpleGraph V) : Prop :=
  ∃ M : Fin 3 → PerfectMatching G, (M 0).edges ∩ (M 1).edges ∩ (M 2).edges = ∅

/-- The Máčajová–Škoviera property: there are two perfect matchings whose intersection
contains no odd edge cut. -/
def MacajovaSkoviera (G : SimpleGraph V) : Prop :=
  ∃ M₁ M₂ : PerfectMatching G, ∀ C, IsOddCut G C → ¬ C ⊆ M₁.edges ∩ M₂.edges

/-- A proper 3-edge-colouring of a (cubic) graph: a partition of the edge set into three
perfect matchings. -/
def ProperThreeEdgeColoring (G : SimpleGraph V) : Prop :=
  ∃ M : Fin 3 → PerfectMatching G,
    (∀ i j, i ≠ j → Disjoint (M i).edges (M j).edges) ∧
    (∀ e ∈ G.edgeSet, ∃ i, e ∈ (M i).edges)

/-- `G` is cubic if every vertex has exactly three neighbours. -/
def IsCubic (G : SimpleGraph V) : Prop := ∀ v : V, (G.neighborSet v).ncard = 3

/-- `G` is bridgeless if no edge is a bridge (in the sense of `SimpleGraph.IsBridge`). -/
def Bridgeless (G : SimpleGraph V) : Prop := ∀ e ∈ G.edgeSet, ¬ G.IsBridge e

/-! ## The implications BF ⟹ FR ⟹ MŠ -/




/-! ## Bridgelessness is necessary: one-edge odd cuts destroy all three properties -/






/-! ## 3-edge-colourable graphs satisfy Berge–Fulkerson -/


/-! ## Invariance under isomorphism -/

namespace PerfectMatching

variable {W : Type v} {H : SimpleGraph W}

/-- Transport a perfect matching along a graph isomorphism. -/
def map (f : G ≃g H) (M : PerfectMatching G) : PerfectMatching H where
  partner w := f (M.partner (f.symm w))
  isAdj w := by
    have h := f.map_adj_iff.mpr (M.isAdj (f.symm w))
    simpa using h
  invol w := by simp [M.invol]



end PerfectMatching






end Bridges.InfiniteCubicMatchings


