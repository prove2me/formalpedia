-- Prove2me | Definitions.Def_MachineLearning_TropicalGraph
-- name    : MachineLearning_TropicalGraph
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T19:17:14.208523+00:00
-- url     : https://prove2.me/theorems/97d96db1-9300-4d3b-bf67-d00214444649
-- title:
--   Aether Catalog definitions — MachineLearning_TropicalGraph
-- statement:
--   Definition bundle for the Aether Catalog module `MachineLearning.TropicalGraph`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from MachineLearning/TropicalGraph.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Tropical Graph Optimization for Stellar Energy Collection

## Overview

This file formalizes the connection between tropical (min-plus) optimization
on finite weighted graphs and energy collection on discretized stellar shells.

The key insight is that maximizing energy gain at panel sites reduces to
minimizing tropical (shortest-path) distance from the stellar source.
This provides a certified algebraic bridge between:
- **Tropical algebra** (min-plus semiring operations),
- **Combinatorial optimization** (shortest paths on finite graphs),
- **Energy network design** (optimal panel placement on stellar shells).

## Main Results

* `tropical_plus_distributes_over_min` — The key distributive law
  `a + min b c = min (a + b) (a + c)` underlying Bellman recursion.
* `argmax_gain_eq_argmin_dist` — Maximizing panel gain ↔ minimizing
  tropical distance: the core optimization equivalence.
* `symmetric_graph_nonunique_optimizers` — Equal tropical distances
  yield equal gains, formalizing degeneracy of optimal configurations.
* `bellman_step` — One-step Bellman relaxation: extending shortest paths
  through predecessors.
* `path_cost_concat` — Path cost decomposes under concatenation.

## Physical Interpretation

- **Vertices** = panel sites on a shell discretization.
- **Edge weights** = transport/routing/conversion losses between sites.
- **Tropical distance** = minimum total loss from stellar source to a site.
- **Gain** = incident flux minus tropical distance = net collected energy.

The optimization equivalence theorem certifies that optimal energy collection
reduces to a standard shortest-path computation in the min-plus semiring.
-/

open Classical

namespace TropicalDyson

/-! ## §1. Tropical Algebra Foundations

The min-plus semiring (ℝ, min, +) has two operations:
- **Tropical addition**: `a ⊕ b = min a b` (route selection)
- **Tropical multiplication**: `a ⊗ b = a + b` (loss accumulation)

The distributive law `a ⊗ (b ⊕ c) = (a ⊗ b) ⊕ (a ⊗ c)` translates to
`a + min b c = min (a+b) (a+c)`, which is the algebraic engine of
dynamic programming for shortest paths.
-/

/-
**Tropical Distributivity**: Addition distributes over min.
    This is the foundational identity for Bellman-style dynamic programming
    in the min-plus semiring. It allows path extension (adding edge cost `a`)
    to commute with route selection (taking the min over predecessors).
-/

/-
Commutativity of tropical addition (min).
-/

/-
Idempotency of tropical addition: selecting among identical options
    yields the same option.
-/

/-
Right-distributivity of addition over min.
-/

/-
**Tropical non-injectivity**: min is not injective —
    distinct inputs can yield the same output. This is the algebraic
    manifestation of multiple equally optimal configurations.
-/

/-! ## §2. Finite Graph Tropical Distance

We model a stellar shell discretization as a finite weighted directed graph.
Vertices are panel sites, and edge weights represent transport/conversion losses.
-/

/-- Edge weight function on a graph with vertex type `V`.
    `w u v` is the cost (loss) of routing energy from site `u` to site `v`. -/
def EdgeWeight (V : Type*) := V → V → ℝ

/-- Cost of traversing a path given by a list of vertices.
    In the min-plus semiring, this is the tropical product of edge weights
    along the path. Empty paths and single vertices have zero cost. -/
def pathCost {V : Type*} (w : EdgeWeight V) : List V → ℝ
  | [] => 0
  | [_] => 0
  | a :: b :: t => w a b + pathCost w (b :: t)

/-- A valid path from `s` to `t`: nonempty, starts at `s`, ends at `t`. -/
def validPath {V : Type*} (s t : V) (p : List V) : Prop :=
  p ≠ [] ∧ p.head? = some s ∧ p.getLast? = some t

/-
Path cost decomposes additively under single-step extension:
    appending an edge `(a, b)` adds `w a b` to the cost.
-/

/-
The trivial self-path `[v]` is a valid path from `v` to `v`.
-/

/-
The trivial self-path has zero cost.
-/

/-- **Tropical distance** from source `s` to target `t`:
    the infimum of path costs over all valid paths.
    This is the shortest-path distance in the min-plus semiring. -/
noncomputable def tropicalDist {V : Type*} [Fintype V] [DecidableEq V]
    (w : EdgeWeight V) (s t : V) : ℝ :=
  sInf {c : ℝ | ∃ p, validPath s t p ∧ pathCost w p = c}

/-- **Panel gain** at vertex `v` from stellar source `s` with incident
    flux parameter `G`. Gain equals incident flux minus transport loss,
    where transport loss is the tropical distance from the source. -/
noncomputable def gainAt {V : Type*} [Fintype V] [DecidableEq V]
    (w : EdgeWeight V) (s : V) (G : ℝ) (v : V) : ℝ :=
  G - tropicalDist w s v

/-! ## §3. Core Optimization Equivalence

The central theorem: maximizing energy gain is equivalent to minimizing
tropical distance. This bridges max-throughput energy collection with
min-cost tropical routing.
-/

/-
**Tropical Optimization Equivalence**: A vertex `u` maximizes energy
    gain from source `s` if and only if it minimizes tropical distance
    from `s`.

    Physically: the best panel placement (maximum energy collection) is
    exactly the site with minimum transport/routing loss.

    The proof reduces to the order-reversing property of subtraction from
    a constant: `G - d_u ≥ G - d_v ↔ d_u ≤ d_v`.
-/

/-
**Non-unique Optimizers (Tropical Degeneracy)**: If two vertices have
    equal tropical distance from the source, they achieve equal gain.

    This formalizes a key physical insight: symmetric placement of solar
    panels on a Dyson sphere yields identical energy collection efficiency.
    Multiple shell configurations can be equally optimal — a theorem-level
    manifestation of degeneracy in tropical optimization.
-/

/-! ## §4. Bellman Dynamic Programming

The Bellman principle for tropical shortest paths: the optimal cost to
reach a vertex `v` decomposes into a one-step extension from some
predecessor `u`. This is the dynamic programming foundation for
computing tropical distances on finite graphs.
-/

/-
One-step Bellman relaxation: if there is a path from `s` to `u`
    with cost `c`, then there is a path from `s` to `v` through `u`
    with cost `c + w u v`.

    This is the path-extension principle that drives DP computation
    of tropical distances.
-/

/-
Path cost of a two-vertex path equals the edge weight.
-/

/-! ## §5. Tropical Capacity and Network Optimization

The tropical capacity of a network captures the best achievable
transport efficiency across all panel sites.
-/

/-- **Tropical capacity** of a network: the minimum tropical distance
    achievable from source `s` to any vertex. Lower capacity means
    more efficient energy routing.

    This is the network-level analogue of channel capacity in
    information theory, expressed in the min-plus semiring. -/
noncomputable def tropicalCapacity {V : Type*} [Fintype V] [DecidableEq V]
    (w : EdgeWeight V) (s : V) : ℝ :=
  ⨅ v : V, tropicalDist w s v

/-
The tropical distance to any vertex is at least the tropical capacity.
-/

/-
The maximum gain over all vertices equals `G - tropicalCapacity`.
-/

end TropicalDyson


