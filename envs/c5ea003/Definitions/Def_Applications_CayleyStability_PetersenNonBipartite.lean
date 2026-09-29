-- Prove2me | Definitions.Def_Applications_CayleyStability_PetersenNonBipartite
-- name    : Applications_CayleyStability_PetersenNonBipartite
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:39:18.07479+00:00
-- url     : https://prove2.me/theorems/b68cb1c6-0cb9-4bf4-9a0e-e666a4fcda43
-- title:
--   Aether Catalog definitions — Applications_CayleyStability_PetersenNonBipartite
-- statement:
--   Definition bundle for the Aether Catalog module `Applications.CayleyStability.PetersenNonBipartite`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Applications/CayleyStability/PetersenNonBipartite.lean by skeleton subtraction
import Mathlib
/-
# The Petersen graph is not bipartite (odd girth 5)

This file gives a self-contained construction of the **Petersen graph** as the
Kneser graph `K(5,2)` — vertices are the two-element subsets of `Fin 5` and two
vertices are adjacent when the subsets are disjoint — and proves the structural
fact underlying every non-embeddability result in this development:

* `Petersen_not_colorable_two` : the Petersen graph is **not** `2`-colorable,
  i.e. it is not bipartite.

The proof exhibits a concrete odd closed walk (`petersenPentagon`, one of the
graph's `5`-cycles) and invokes the Mathlib characterization
`SimpleGraph.two_colorable_iff_forall_loop_even`: a graph is bipartite iff every
closed walk has even length.  A closed walk of length `5` therefore falsifies
bipartiteness.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The Petersen graph, being vertex-transitive with odd
girth `5`, contains an odd closed walk and hence cannot be `2`-colored.  This is
the seed obstruction: any host graph that IS bipartite cannot receive the
Petersen graph as an isometric (indeed even as an edge-preserving) subgraph.

Experiment (Experimenter): Formalised the Kneser model `K(5,2)` via a `Finset`
subtype `PetersenV = {s : Finset (Fin 5) // s.card = 2}` and adjacency by
`Disjoint`.  Built an explicit pentagon
`{0,1}-{2,3}-{4,0}-{1,2}-{3,4}-{0,1}` as a `SimpleGraph.Walk`, each edge
discharged by `decide`.  Non-`2`-colorability follows from the closed walk of
odd length `5` via `two_colorable_iff_forall_loop_even`.

Analysis (Analyst): The subtype model makes both adjacency (`Disjoint`) and the
cardinality side-conditions decidable, so the entire combinatorial content is a
`decide`.  The mathematically load-bearing step is the Mathlib bridge between
`2`-colorability and parity of closed walks — not `decide` — which is what keeps
the theorem from being a pure computation.

Critique (Critic): `decide` alone cannot prove `¬ Colorable 2` (colorability
quantifies over all colorings and is not set up for kernel reduction here); the
proof genuinely routes through the walk-parity theorem and an explicit witness
walk, so it is not a disguised `native_decide`.

Synthesis (PI): `Petersen_not_colorable_two` is exported as the combinatorial
core consumed by `PetersenAbelianCayley.lean`, where it is combined with a
metric (isometric-embedding) obstruction to rule out bipartite abelian Cayley
hosts, including all hypercubes.
-- !-- end Lab Notes -- !--
-/

open SimpleGraph

namespace PetersenGraph

/-- Vertices of the Petersen graph: the two-element subsets of `Fin 5`
(the Kneser graph `K(5,2)`). -/
def PetersenV := {s : Finset (Fin 5) // s.card = 2}

instance : DecidableEq PetersenV := by unfold PetersenV; infer_instance
instance : Fintype PetersenV := by unfold PetersenV; infer_instance

/-- The **Petersen graph** as the Kneser graph `K(5,2)`: two two-element
subsets of `Fin 5` are adjacent iff they are disjoint. -/
def Petersen : SimpleGraph PetersenV :=
  SimpleGraph.fromRel (fun s t => Disjoint s.1 t.1)

instance : DecidableRel Petersen.Adj := fun a b => by
  unfold Petersen SimpleGraph.fromRel; infer_instance

/-- Five vertices of one of the Petersen graph's `5`-cycles. -/
def v01 : PetersenV := ⟨{0, 1}, by decide⟩
def v23 : PetersenV := ⟨{2, 3}, by decide⟩
def v40 : PetersenV := ⟨{4, 0}, by decide⟩
def v12 : PetersenV := ⟨{1, 2}, by decide⟩
def v34 : PetersenV := ⟨{3, 4}, by decide⟩

/-- An explicit odd closed walk of length `5` (a pentagon) in the Petersen
graph, based at `v01`. -/
def petersenPentagon : Petersen.Walk v01 v01 :=
  .cons (show Petersen.Adj v01 v23 by decide)
    (.cons (show Petersen.Adj v23 v40 by decide)
      (.cons (show Petersen.Adj v40 v12 by decide)
        (.cons (show Petersen.Adj v12 v34 by decide)
          (.cons (show Petersen.Adj v34 v01 by decide) .nil))))


end PetersenGraph


