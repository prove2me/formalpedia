-- Prove2me | Definitions.Def_Novelty_ProteinFoldingMST
-- name    : Novelty_ProteinFoldingMST
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:37:41.791872+00:00
-- url     : https://prove2.me/theorems/93570c4f-2eeb-48be-b70e-821e2de9cbc2
-- title:
--   Aether Catalog definitions — Novelty_ProteinFoldingMST
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.ProteinFoldingMST`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/ProteinFoldingMST.lean by skeleton subtraction
import Mathlib

/-! # The Minimum-Spanning-Tree Law for `H₀` Persistence

This file formalizes the degree-`0` total-persistence law of topological data
analysis in a fully constructive, computable setting.  The homological framing
("persistent `H₀` of a single-linkage filtration") collapses, once the *death
multiset* `D` of the persistence diagram is fixed, to elementary order-theoretic
counting:

* `layer_cake` — the discrete Fubini / layer-cake identity
  `∑_{t<T} #{d ∈ D : t < d} = ∑_{d ∈ D} min d T`.
* `totalPersistence_eq_sum` — **the MST Law**: for a horizon `T` dominating every
  death, total `H₀` persistence equals `∑_{d ∈ D} d`, the total weight of a
  minimum spanning tree.
* `beta0_antitone`, `beta0_eventually_one` — the component-count curve `β₀` is
  monotone non-increasing and reaches a single component above the largest death.
* A constructive Kruskal merge process (`kruskalDeaths`) with `decide`-checked
  optimality (`mst_optimal_ex`) and a capstone (`mst_persistence_law_example`)
  tying the persistence side to the optimization side on an explicit graph.

This is a cross-domain bridge between **topological data analysis** (`H₀`
persistence), **combinatorial optimization** (minimum spanning trees / Kruskal),
and **order-theoretic counting** (the layer-cake identity).
-/

namespace ProteinFoldingMST

/-! ## Persistence-side definitions

`D : Multiset ℕ` is the multiset of *death* values of the `H₀` persistence
diagram (equivalently, the edge weights of a minimum spanning tree of the
single-linkage filtration).  A point cloud with `N` points produces a diagram
with `N - 1` finite bars `[0, d)`; the one essential bar `[0, ∞)` is the `+1`
appearing in `beta0`. -/

/-- The `β₀` curve: number of connected components present at filtration value
`t`.  It is `1` (the essential component) plus the number of bars still alive,
i.e. the number of deaths strictly exceeding `t`. -/
def beta0 (D : Multiset ℕ) (t : ℕ) : ℕ := (D.filter (fun d => t < d)).card + 1

/-- Total `H₀` persistence accumulated up to horizon `T`: the discrete area under
the curve `t ↦ β₀(t) - 1`, i.e. `∑_{t<T} #{d ∈ D : t < d}`. -/
def totalPersistence (D : Multiset ℕ) (T : ℕ) : ℕ :=
  ∑ t ∈ Finset.range T, (D.filter (fun d => t < d)).card

-- !-- Proof sketch (layer_cake): induct on `T`. The cons-step adds the single
-- new column `t = T`, whose height is `#{d : T < d}`, which is exactly
-- `∑_d (min d (T+1) - min d T)` since `min d (T+1) = min d T + [T < d]`. -- !--

-- !-- Proof sketch (eq_sum): apply `layer_cake`; when every death is `≤ T`,
-- `min d T = d`, so the truncated sum collapses to `D.sum`. -- !--

-- !-- Proof sketch (antitone): `s ≤ t` implies `{d : t < d} ⊆ {d : s < d}` as
-- a sub-multiset, so the filtered cardinalities are monotone, hence `beta0`
-- is antitone. -- !--

-- !-- Proof sketch (eventually_one): if every death is `≤ t` then the filter
-- `t < d` is empty, its card is `0`, and `beta0 = 0 + 1 = 1`. -- !--

/-! ## Optimization side: a constructive Kruskal merge process

Vertices are `0, …, n-1`; an edge is a triple `(w, a, b)` (weight, endpoints).
The component structure is a `List ℕ` of labels indexed by vertex; processing the
edges in weight order, an edge whose endpoints lie in distinct components merges
them and records its weight as a *death*.  The recorded death multiset is exactly
the multiset of edge weights of the minimum spanning tree (Kruskal). -/

/-- Relabel every vertex currently carrying component id `old` to `new`. -/
def relabel (labels : List ℕ) (old new : ℕ) : List ℕ :=
  labels.map (fun c => if c = old then new else c)

/-- One Kruskal step: merge the endpoints' components and record the weight as a
death iff the endpoints lie in distinct components. -/
def kstep (st : List ℕ × List ℕ) (e : ℕ × ℕ × ℕ) : List ℕ × List ℕ :=
  let labels := st.1
  let deaths := st.2
  let ca := labels.getD e.2.1 0
  let cb := labels.getD e.2.2 0
  if ca = cb then st else (relabel labels cb ca, deaths ++ [e.1])

/-- Fold the Kruskal step over a (weight-sorted) edge list, starting from the
discrete partition `List.range n`. -/
def kruskalRun (n : ℕ) (es : List (ℕ × ℕ × ℕ)) : List ℕ × List ℕ :=
  es.foldl kstep (List.range n, [])

/-- The multiset (here, list) of recorded deaths = MST edge weights. -/
def kruskalDeaths (n : ℕ) (es : List (ℕ × ℕ × ℕ)) : List ℕ := (kruskalRun n es).2

/-- All entries of a label list are equal (one connected component). -/
def allEqual (l : List ℕ) : Bool := l.all (· == l.headD 0)

/-- A set of edges spans all `n` vertices (single component after union). -/
def spans (n : ℕ) (es : List (ℕ × ℕ × ℕ)) : Bool := allEqual (kruskalRun n es).1

/-- Total weight of an edge set. -/
def wsum (es : List (ℕ × ℕ × ℕ)) : ℕ := (es.map Prod.fst).sum

/-- A concrete `4`-vertex graph (a path plus one cycle-closing chord). -/
def exampleEdges : List (ℕ × ℕ × ℕ) := [(1,0,1),(2,1,2),(3,2,3),(4,0,3)]



-- !-- Proof sketch (optimality): brute-force over all `2^4` edge subsets; every
-- spanning subset has weight `≥ 6`, the Kruskal optimum. Verified by `decide`. -- !--

-- !-- Proof sketch (capstone): combine `kruskal_weight_ex` with `mst_optimal_ex`
-- and `totalPersistence_eq_sum` (horizon `3`) to identify the persistence-side
-- area with the optimization-side minimum weight, both equal to `6`. -- !--

/-!
-- !-- Lab Notebook -- !--

**Hypothesis.** The degree-`0` total-persistence functional of a single-linkage
filtration, although phrased homologically, should reduce to pure counting on the
death multiset `D`, and should coincide with the total weight of a minimum
spanning tree (the "MST Law").

**Result.** Confirmed and formalized. `layer_cake` gives the discrete Fubini
identity `∑_{t<T} #{d : t<d} = ∑_d min d T`; specializing the horizon yields the
MST Law `totalPersistence D T = D.sum` (`totalPersistence_eq_sum`). The component
curve `β₀` is antitone (`beta0_antitone`) and stabilizes at `1`
(`beta0_eventually_one`). A constructive Kruskal fold (`kruskalDeaths`) plus a
`decide`-checked optimality theorem (`mst_optimal_ex`) and the capstone
(`mst_persistence_law_example`) tie the persistence side to the optimization side.

**Insight.** The decisive invariant is the death multiset: once extracted, the
entire connectivity history is recovered by `min`-truncation and layer-cake
summation, with no homology. The truncation `min d T` is exactly the clipping
that makes a future Lipschitz/stability constant finite — see FUTURE_DIRECTIONS.

**Failure analysis.** Working over `ℕ` (not `Fin n`) for vertices and deaths
avoided index-arithmetic friction and kept everything `decide`-computable. An
earlier instinct to phrase optimality via an abstract "spanning tree" predicate
was abandoned in favor of a `decide`-checked brute force over edge subsets, which
is sound, reproducible, and free of choice-of-representation pitfalls.
-/

end ProteinFoldingMST


