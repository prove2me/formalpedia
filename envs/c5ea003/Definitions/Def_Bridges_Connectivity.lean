-- Prove2me | Definitions.Def_Bridges_Connectivity
-- name    : Bridges_Connectivity
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:19:21.321713+00:00
-- url     : https://prove2.me/theorems/519afbab-2596-4705-83e0-09fc0a89a9cb
-- title:
--   Aether Catalog definitions — Bridges_Connectivity
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.Connectivity`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/Connectivity.lean by skeleton subtraction
import Mathlib

/-!
# Vertex `k`-connectivity and the degree necessary condition

Mathlib has edge connectivity and `Connected`, but no notion of vertex
`k`-connectivity (the object at the heart of the connectivity-preserving
Hamiltonian-path program of Hasunuma 2025 and the prescribed-end strengthening).
We supply the standard cut-based definition and prove the classical
**necessary degree condition** that vertex `k`-connectivity forces minimum degree
at least `k` — the easy half of the Whitney/Menger inequality
`κ(G) ≤ δ(G)`.

## Main definitions and results

* `IsKConnected G k` — `G` has more than `k` vertices and deleting any fewer
  than `k` vertices leaves a connected graph.
* `Connected.exists_adj_of_ne` — in a connected graph with two distinct
  vertices, every vertex has a neighbor.
* `IsKConnected.le_ncard_neighborSet` — **`κ(G) ≤ δ(G)`**: in a
  `k`-connected graph every vertex has degree at least `k`.
* `Conjecture_4k4` — the precise (open) research conjecture, recorded as a `Prop`.

-- !-- Lab Notes -- !--
* Hypothesis (Hypothesizer): for a connectivity-preserving deletion theorem one
  must control connectivity, so a vertex-cut definition is unavoidable.  We
  conjectured the classical `κ ≤ δ` bound holds with the cut-based definition.
* Experiment (Experimenter): defined `IsKConnected` via induced subgraphs on
  vertex-set complements and proved `κ ≤ δ` by the textbook argument — if some
  vertex `w` had degree `< k`, its neighborhood is a cut of size `< k` isolating
  `w`, contradicting connectivity of the deletion.
* Analysis (Analyst): the proof needs the "no isolated vertex in a connected
  graph on `≥ 2` vertices" lemma (`exists_adj_of_ne`), extracted separately.
  The cardinality slack `card V - (k-1) ≥ 2` is exactly where `k < card V`
  is consumed (the `h_singleton` case split).
* Critique (Critic): this is only the *necessary* direction. The converse
  (Chartrand–Harary: `δ ≥ (n+k-2)/2 ⇒ κ ≥ k`) is strictly deeper and is *not*
  claimed here; it is recorded as a future direction.  The definition is guarded
  by `k < card V` so the empty/complete-graph corner cases are handled.
-- !-- end Lab Notes -- !--
-/

open SimpleGraph

namespace ConnPreservingHamPath

variable {V : Type*}

/-- `G` is (vertex) `k`-connected: it has more than `k` vertices and removing
any set of fewer than `k` vertices leaves a connected induced subgraph. -/
def IsKConnected [Fintype V] (G : SimpleGraph V) (k : ℕ) : Prop :=
  k < Fintype.card V ∧
    ∀ S : Finset V, S.card < k → (G.induce ((↑S : Set V)ᶜ)).Connected




end ConnPreservingHamPath


