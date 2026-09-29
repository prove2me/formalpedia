-- Prove2me | Theorems.Thm_CycleParityQuotient_tri_graph_dist
-- name    : CycleParityQuotient.tri_graph_dist
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:29:24.773023+00:00
-- url     : https://prove2.me/theorems/b9bd31c1-3ccc-4c89-ae66-d33dc1fb0b81
-- title:
--   The graph distance across the edge `{0,2}` of the triangle is `1`.
-- statement:
--   The graph distance across the edge `{0,2}` of the triangle is `1`.
--
--   ```lean
--   theorem CycleParityQuotient.tri_graph_dist: (⊤ : SimpleGraph (Fin 3)).dist 0 2 = 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Applications/GraphTheory/CycleParityQuotientNoStretch.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Applications/GraphTheory/CycleParityQuotientNoStretch.lean#L164

-- Thm stub generated from Applications/GraphTheory/CycleParityQuotientNoStretch.lean
import Mathlib
import Definitions.Def_Applications_GraphTheory_CycleParityQuotientNoStretch
/-
Copyright (c) 2026. All rights reserved.

# No-stretching for GF(2) quotient labelings from edge partitions

Let `G` be a connected simple graph with an edge partition into `t` classes.  Associating a `GF(2)`
generator `gen i` with each class `i` and quotienting the ambient parity space `(Fin t → ZMod 2)` by
the *cycle-class parity space* `C` produces a labeling `ℓ : V → Q` into the abelian `2`-group
`Q = (Fin t → ZMod 2) ⧸ C`, whose dimension is `t - rank(A)` where `A` is the cycle-class parity
matrix and `rank(A) = dim C`.

The defining local property of this labeling is that adjacent vertices either receive the same label
or differ by a single class generator.  We prove the **no-stretching** property:

  `d_H(ℓ u, ℓ v) ≤ d_G(u, v)`,

where `H` is the **Cayley graph** of `Q` on the generating set `{gen i}`.  The labeling can only
contract distances (shortcuts), never stretch them.

The heart of the argument is a general fact about *edge-contracting* graph maps
(`dist_contract`): any vertex map that sends adjacent vertices to adjacent-or-equal vertices is
distance non-increasing.  This is the discrete analogue of a `1`-Lipschitz map and it directly
generalizes the hypercube no-stretching result in `Catalog/Applications/HypercubeNoStretch.lean` from
the coordinate hypercube to an arbitrary Cayley graph of an abelian `2`-group.

## Main results

* `dist_contract` — edge-contracting maps do not stretch graph distance.
* `cayley_no_stretch` — a labeling compatible with a symmetric generating set does not stretch
  distances into the Cayley graph.
* `cayley_no_stretch_partition` — the edge-partition / class-generator form of the theorem.
* `quotient_finrank` — the quotient target has dimension `t - rank(A)`.
* `tri_cayley_no_stretch` / `tri_hamming_stretches` — a concrete triangle showing that the naive
  *coordinate-hypercube* (Hamming) interpretation **stretches** distances, whereas the Cayley-graph
  interpretation does not.  This pins down the correct target graph `H`.
-/

open SimpleGraph

open CycleParityQuotient

/-! ## Core: edge-contracting maps do not stretch distance -/



/-! ## The Cayley graph of an abelian `2`-group -/



/-! ## No-stretching of quotient labelings -/



/-! ## The quotient dimension `t - rank(A)` -/


/-! ## A triangle: the Cayley target is right, the coordinate hypercube is wrong

The triangle `K₃` with all three edges in distinct classes has a one-dimensional cycle-class parity
space `C = ⟨(1,1,1)⟩`, so the quotient is `(ZMod 2)^2`.  The class generators become
`gen 0 = (1,0)`, `gen 1 = (0,1)`, `gen 2 = (1,1)`, and the quotient labeling is
`lab 0 = (0,0)`, `lab 1 = (1,0)`, `lab 2 = (1,1)`.

The edge `{0,2}` (class `2`) is a *single* Cayley step `gen 2 = (1,1)`, so `d_H(lab 0, lab 2) = 1`,
matching `d_G(0,2) = 1`.  But in the *coordinate hypercube* with Hamming distance,
`(0,0)` and `(1,1)` are at distance `2` — the labeling would appear to **stretch** an edge.  This is
why the correct target is the Cayley graph on the class generators, not the coordinate hypercube. -/

theorem CycleParityQuotient.tri_graph_dist: (⊤ : SimpleGraph (Fin 3)).dist 0 2 = 1 := by sorry
