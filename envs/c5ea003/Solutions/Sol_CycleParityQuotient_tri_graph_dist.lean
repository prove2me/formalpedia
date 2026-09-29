-- Prove2me | solution 1 for CycleParityQuotient.tri_graph_dist
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:12:18.130277+00:00
-- url     : https://prove2.me/submissions/f0812005-3be3-4054-be1c-aeafa258f2e6

-- Sol generated from Applications/GraphTheory/CycleParityQuotientNoStretch.lean
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










/-
-- !-- Lab Notes -- !--

HYPOTHESIS (Hypothesizer).
  For a connected graph G with an edge partition into t classes, the GF(2) quotient labeling
  ℓ : V → (ZMod 2)^t ⧸ C (C = cycle-class parity space, dim = rank A) satisfies
  d_G(u,v) ≥ d_H(ℓ u, ℓ v). Bold sub-conjecture: H is literally the coordinate hypercube on
  (ZMod 2)^(t - rank A) with Hamming distance.

EXPERIMENT (Experimenter).
  Abstracted the mechanism to the reusable lemma `dist_contract`: any vertex map sending adjacent
  vertices to adjacent-OR-equal vertices is distance non-increasing (proved by walk induction with
  Walk.copy to absorb contracted edges). Instantiated it at the Cayley graph of an abelian 2-group
  (`cayley_no_stretch`, `cayley_no_stretch_partition`) and confirmed the dimension count
  `t - rank A` via rank–nullity (`quotient_finrank`).

ANALYSIS (Analyst).
  The general no-stretching theorem is TRUE and clean: each edge is exactly one generator step, so
  it maps to one Cayley edge (or a fixed point when the generator lies in C). The bold
  coordinate-hypercube sub-conjecture is FALSE. On K₃ with three singleton classes, C = ⟨(1,1,1)⟩,
  and gen 2 = (1,1) has Hamming weight 2. So the edge {0,2} — graph distance 1 — has label Hamming
  distance 2: a stretch. The failure is structural, not an artifact: a linear quotient of GF(2)^t is
  Hamming-non-expanding only when the generators map to coordinate directions, which fails whenever a
  cycle forces a generator to be a sum of others.

CRITIQUE (Critic).
  Is the counterexample vacuous? No: `tri_cayley_adj` shows the labels ARE Cayley-adjacent (distance
  ≤ 1) while `tri_hamming_stretches` shows Hamming distance 2 > graph distance 1, with
  `tri_graph_dist` proving the graph distance is genuinely 1 (not 0). So the same labeling
  simultaneously satisfies no-stretching in the Cayley target and violates it in the coordinate
  hypercube. The theorem `cayley_no_stretch` uses induction/rcases/by_cases (non-trivial), not
  `decide`. The concrete finite facts (`gen_symm`, `tri_edge_gen`, Hamming value) are discharged by
  `decide`, but they are lemmas feeding genuine theorems, not the main results.

SYNTHESIS (PI).
  The correct statement of the no-stretching property must take H to be the Cayley graph of the GF(2)
  quotient on the class generators; the coordinate-hypercube reading holds only in the corank-0
  (forest-like / partial-cube) regime where the generators stay independent. `dist_contract`
  generalizes the sibling result `HypercubeNoStretch.no_stretching` from Hamming to any Cayley
  target, unifying both under "edge-contracting maps don't stretch distance".
-/
open CycleParityQuotient in
theorem solution: (⊤ : SimpleGraph (Fin 3)).dist 0 2 = 1 := by
  have hadj : (⊤ : SimpleGraph (Fin 3)).Adj 0 2 := by simp [SimpleGraph.top_adj]
  refine le_antisymm ?_ ?_
  · calc (⊤ : SimpleGraph (Fin 3)).dist 0 2 ≤ (Walk.cons hadj Walk.nil).length :=
          SimpleGraph.dist_le _
      _ = 1 := by simp [Walk.length]
  · rw [Nat.one_le_iff_ne_zero]
    intro hc
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable] at hc
    rcases hc with h | h
    · exact (by decide : (0 : Fin 3) ≠ 2) h
    · exact h (connected_top.preconnected 0 2)
