-- Prove2me | Definitions.Def_Novelty_SparseThresholdFractionalIndependence
-- name    : Novelty_SparseThresholdFractionalIndependence
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T14:41:25.208193+00:00
-- url     : https://prove2.me/theorems/3d2859b8-2c6b-48dd-9d61-72db3757489e
-- title:
--   Aether Catalog definitions — Novelty_SparseThresholdFractionalIndependence
-- statement:
--   Definition bundle for the Aether Catalog module `Novelty.SparseThresholdFractionalIndependence`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Novelty/SparseThresholdFractionalIndependence.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The fractional independence number `α*(H)` and its sparse-threshold bounds

The sparse threshold conjecture of Day & Sarkar predicts that the exponent and the extremal
graphon of the sparse subgraph-density problem are controlled by the **fractional independence
number** `α*(H)`: the value of the linear-programming relaxation of the independence number,

  `α*(H) = max { Σ_v x_v : 0 ≤ x_v ≤ 1, and x_u + x_v ≤ 1 for every edge uv }`.

This file gives a clean, self-contained Lean development of `α*` as a real supremum over the
feasible polytope of a finite simple graph, and proves the structural bounds that the threshold
theory needs:

* the polytope value is always bounded by the number of vertices (`alphaStar_le_card`);
* the all-`½` assignment is feasible, giving the universal lower bound `|V|/2 ≤ α*(H)`
  (`half_card_le_alphaStar`);
* a single edge already forces `α*(H) ≤ |V| - 1` (`alphaStar_le_card_sub_one_of_edge`), so a
  graph **without isolated vertices** never has the trivial value `|V|`;
* for the complete graph the universal lower bound is *tight*: `α*(K_n) = n/2`
  (`alphaStar_completeGraph`).

## Catalog connections
* `Fractional independence number α*(H)`: `alphaStar` is precisely this LP value, here built as a
  genuine `sSup` over the feasible set.
* `Day & Sarkar's sparse threshold conjecture`: `half_card_le_alphaStar` and
  `alphaStar_le_card_sub_one_of_edge` are the structural inputs that pin the conjectured exponent.
* `Three-step threshold graphon characterization`: the half-integral extremal structure of the
  `α*`-polytope mirrors the three-block structure of the extremal graphon.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): `α*(H)` is sandwiched as `|V|/2 ≤ α*(H) ≤ |V|`, with the lower bound
  attained by the densest graphs (complete graphs) and the upper bound never attained once `H`
  has an edge.  The half-integral "all-½" point is the universal certificate for the lower bound.
Experiment (Experimenter): Defined feasibility (`0 ≤ x ≤ 1`, plus the edge constraints) and the
  value `Σ_v x_v`, then `alphaStar := sSup (valueSet)`.  Proved boundedness (`Σ x ≤ card`) and
  nonemptiness (`x = 0`), so the `sSup` is well-behaved.  Lower bound: the constant `½` assignment
  is feasible with value `card/2`, apply `le_csSup`.  Complete-graph upper bound: double count
  `Σ_u Σ_{v≠u} (x_u + x_v) ≤ n(n-1)` to get `(2n-2)·Σ x ≤ n(n-1)`, hence `Σ x ≤ n/2`.
Analysis (Analyst): The double-count is the LP-dual fractional vertex cover in disguise; the
  factor `2n-2` is `2(n-1)` because each vertex appears in `n-1` complete-graph edges.  The
  "no isolated vertices ⇒ α* < |V|" phenomenon is captured by the single-edge bound: one edge
  caps the two endpoints' joint contribution at `1` instead of `2`.
Critique (Critic): The `sSup` could be vacuous if the feasible set were empty or unbounded; both
  are ruled out (nonempty via `x=0`, bounded via `x ≤ 1`).  The complete-graph equality needs
  `2 ≤ n` (at `n=1`, `K_1` is edgeless and `α* = 1 ≠ 1/2`); we keep that hypothesis honestly.
Synthesis (PI): A reusable LP-style `α*` with the exact sandwich the threshold conjecture uses,
  feeding the exponent of `Catalog/Novelty/SparseThresholdVariational.lean`.
-/

open Finset

namespace SparseThreshold

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A point of the fractional-independence polytope of `G`: each coordinate lies in `[0,1]` and
each edge constraint `x u + x v ≤ 1` holds. -/
def FracIndepFeasible (G : SimpleGraph V) (x : V → ℝ) : Prop :=
  (∀ v, 0 ≤ x v ∧ x v ≤ 1) ∧ ∀ u v, G.Adj u v → x u + x v ≤ 1

/-- The value `Σ_v x_v` of a fractional-independence point. -/
def fracIndepValue (x : V → ℝ) : ℝ := ∑ v, x v

/-- The set of achievable values of the fractional-independence LP. -/
def fracIndepValueSet (G : SimpleGraph V) : Set ℝ :=
  {s | ∃ x, FracIndepFeasible G x ∧ s = fracIndepValue x}

/-- The **fractional independence number** `α*(G)`: the value of the LP relaxation of the
independence number, defined as the supremum over the feasible polytope. -/
noncomputable def alphaStar (G : SimpleGraph V) : ℝ := sSup (fracIndepValueSet G)








/-
**The complete-graph value is `n/2`.** The universal lower bound is tight precisely for the
densest graph.
-/

end SparseThreshold


