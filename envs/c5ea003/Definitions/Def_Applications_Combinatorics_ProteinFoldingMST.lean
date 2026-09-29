-- Prove2me | Definitions.Def_Applications_Combinatorics_ProteinFoldingMST
-- name    : Applications_Combinatorics_ProteinFoldingMST
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:30.089366+00:00
-- url     : https://prove2.me/theorems/e797369b-125b-4139-a4d7-701a9f3d19f6
-- title:
--   Aether Catalog definitions — Applications_Combinatorics_ProteinFoldingMST
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.Combinatorics.ProteinFoldingMST`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/Combinatorics/ProteinFoldingMST.lean by skeleton subtraction
import Mathlib

/-! # The Minimum-Spanning-Tree Law for `H₀` Persistence

This file develops, in a fully constructive and computable setting, the
*Minimum-Spanning-Tree (MST) Law* for degree-`0` persistent homology, the
combinatorial backbone of single-linkage clustering used in (among other things)
protein-folding contact analysis.

## The mathematics

Given a finite point cloud with a symmetric weight (distance) function, the
Vietoris–Rips filtration produces a degree-`0` persistence module.  Its finite
bars are born at time `0` and die exactly at the weights of the edges of a
*minimum spanning tree* (Kruskal's algorithm = single-linkage clustering).  Thus
the multiset of **death times** of `H₀` is precisely the multiset of MST edge
weights.

We package the death times as a `Multiset ℕ` `D`.  The connected-component count
at threshold `t` is

  `β₀(t) = 1 + #{ d ∈ D : t < d }`,

i.e. the one essential class plus every finite bar still alive at time `t`.  The
**total `H₀` persistence** up to a horizon `T` is the discrete area under the
`β₀ - 1` curve,

  `P(T) = ∑_{t < T} (β₀(t) - 1)`.

The central theorem (`layer_cake`) is a discrete Fubini / layer-cake identity:

  `∑_{t < T} #{ d ∈ D : t < d } = ∑_{d ∈ D} min d T`,

whose immediate corollary (`totalPersistence_eq_sum`) is the **MST Law**: once
the horizon dominates every death time,

  `P(T) = ∑_{d ∈ D} d`  =  total weight of the minimum spanning tree.

A concrete Kruskal merge process (`kruskalDeaths`) closes the loop computationally:
on an explicit `4`-vertex graph we verify that its death multiset realises the
*minimum* spanning weight (`mst_persistence_law_example`).

-- !-- Lab Notebook -- !--
-- Hypothesis:  Total H₀ persistence (area under the component-count curve) is an
--   exactly computable telescoping quantity, equal to the sum of death times,
--   which under Kruskal's algorithm is the MST weight.
-- Result:  Proved the discrete layer-cake identity `layer_cake` in full
--   generality over `Multiset ℕ`, giving `totalPersistence_eq_sum`.  Verified the
--   Kruskal correspondence and MST optimality computationally on an explicit graph.
-- Insight:  Persistence ↔ MST is, at the level of *counting*, pure Fubini:
--   `∑_t #{d > t} = ∑_d #{t < d} = ∑_d d`.  No homology machinery is needed for
--   the H₀ *total persistence* — only the death multiset, which Kruskal supplies.
-- Failure analysis:  A real-weighted formulation drags in measure-theoretic
--   integration; restricting to `ℕ` weights keeps everything decidable/`#eval`-able
--   while losing no combinatorial content (rationals rescale to ℕ).
-- !-- Lab Notebook -- !--
-/

namespace ProteinFoldingMST

open Finset

/-! ## The `β₀` curve and total persistence -/

/-- `β₀(t)`: the number of connected components at threshold `t`, given the
multiset `D` of `H₀` death times.  It is the one essential (never-dying) class
plus every finite bar still alive at time `t`. -/
def beta0 (D : Multiset ℕ) (t : ℕ) : ℕ := 1 + (D.filter (fun d => t < d)).card

/-- Total `H₀` persistence accumulated up to horizon `T`: the discrete area under
the `β₀ - 1` curve. -/
def totalPersistence (D : Multiset ℕ) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, (beta0 D t - 1)



/-! ## The discrete layer-cake / Fubini identity (heart of the MST Law) -/

/-
!-- The double count `∑_{t<T} #{d∈D : t<d} = ∑_{d∈D} #{t<T : t<d} = ∑_{d∈D} min d T`.
Proven by `Multiset` induction on `D`: the cons step contributes
`∑_{t<T} [t < a] = min a T` on each side. -- !--
-/


/-
**The MST Law for `H₀` persistence.**  Once the horizon `T` dominates every
death time, the total `H₀` persistence equals the sum of the death times — i.e.
the total weight of the minimum spanning tree.

!-- Each `min d T = d` since `d ≤ T`, so the truncated sum is `D.sum`. -- !--
-/

/-! ## Structural properties of the component-count curve -/

/-
`β₀` is antitone in the threshold: raising the connectivity radius can only
merge components, never split them.

!-- Larger `t` shrinks the filtered multiset, hence its card; `Multiset.card_le_card`
of `Multiset.filter_le_filter` (monotone predicate). -- !--
-/

/-
Above the largest death time the cloud is connected: a single component.

!-- All `d ≤ T`, so `filter (T < ·)` is empty and `β₀ T = 1 + 0`. -- !--
-/


/-! ## Constructive Kruskal merge process (single-linkage clustering)

We process edges (already sorted by weight) maintaining a vertex labelling
`ℕ → ℕ` (the component representatives).  An edge whose endpoints lie in distinct
components records a **death** at its weight and merges the two components.  The
resulting death multiset is, by Kruskal's theorem, the multiset of MST edge
weights. -/

/-- One Kruskal step on an edge `(u, v, w)`: if `u, v` are already connected, do
nothing; otherwise relabel and emit the death time `w`. -/
def kstep (f : ℕ → ℕ) (e : ℕ × ℕ × ℕ) : (ℕ → ℕ) × Option ℕ :=
  let u := e.1; let v := e.2.1; let w := e.2.2
  if f u = f v then (f, none)
  else (fun x => if f x = f v then f u else f x, some w)

/-- Fold the Kruskal step over a (weight-sorted) edge list, collecting death
times. -/
def kruskalAux : (ℕ → ℕ) → List (ℕ × ℕ × ℕ) → Multiset ℕ
  | _, [] => 0
  | f, e :: es =>
      let p := kstep f e
      (match p.2 with | none => (0 : Multiset ℕ) | some w => {w}) + kruskalAux p.1 es

/-- The multiset of `H₀` death times produced by Kruskal / single-linkage. -/
def kruskalDeaths (es : List (ℕ × ℕ × ℕ)) : Multiset ℕ := kruskalAux id es

/-! ## Computational verification on an explicit `4`-vertex graph

Vertices `0,1,2,3`; edges listed in increasing weight. -/

/-- An explicit weighted complete-ish graph on `4` vertices, edges sorted by
weight. -/
def exEdges : List (ℕ × ℕ × ℕ) :=
  [(0,1,1),(1,2,2),(0,2,3),(2,3,4),(1,3,5),(0,3,6)]

/-- Neighbours of `x` under an (undirected) edge list. -/
def neighbors (es : List (ℕ × ℕ × ℕ)) (x : ℕ) : List ℕ :=
  es.filterMap (fun e => if e.1 = x then some e.2.1 else if e.2.1 = x then some e.1 else none)

/-- The vertices reachable from `0` (closure, enough iterations for `4` vertices). -/
def reach (es : List (ℕ × ℕ × ℕ)) : List ℕ :=
  (fun S => (S ++ S.flatMap (neighbors es)).dedup)^[4] [0]

/-- Does the edge subset span all of `{0,1,2,3}`? -/
def spans (es : List (ℕ × ℕ × ℕ)) : Bool := [0,1,2,3].all (fun v => v ∈ reach es)

/-- Total weight of an edge subset. -/
def wsum (es : List (ℕ × ℕ × ℕ)) : ℕ := (es.map (·.2.2)).sum





end ProteinFoldingMST


