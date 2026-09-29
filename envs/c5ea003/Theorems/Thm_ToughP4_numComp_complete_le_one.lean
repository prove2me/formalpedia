-- Prove2me | Theorems.Thm_ToughP4_numComp_complete_le_one
-- name    : ToughP4.numComp_complete_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:17:36.878639+00:00
-- url     : https://prove2.me/theorems/9fbd61bc-bd31-437e-a5ec-5120f4c42070
-- title:
--   Deleting any vertex set from a complete graph leaves at most one component:
-- statement:
--   Deleting any vertex set from a complete graph leaves at most one component:
--   every induced subgraph of a complete graph is again complete, hence (pre)connected.
--
--   ```lean
--   theorem ToughP4.numComp_complete_le_one[Fintype V] (S : Finset V) :
--       numComp (⊤ : SimpleGraph V) S ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/MinimallyToughP4Free.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/MinimallyToughP4Free.lean#L115

-- Thm stub generated from Bridges/MinimallyToughP4Free.lean
import Mathlib
import Definitions.Def_Bridges_MinimallyToughP4Free
/-
# Toughness, minimal toughness, and induced `K₁ ∪ P₄`-freeness

Toughness is a quantitative measure of how hard it is to disconnect a graph by
deleting vertices.  A graph `G` is **`1`-tough** if it is connected and, for every
set `S` of vertices, deleting `S` leaves at most `|S|` connected components.
Toughness is a classical *necessary* condition for Hamiltonicity: every graph that
admits a Hamiltonian cycle is `1`-tough (Chvátal).  The converse is famously false
— there exist graphs of arbitrarily high toughness with no Hamiltonian cycle — so
one restricts attention to structured graph classes.  A recurring theme is
**minimal** toughness: `G` is *minimally `1`-tough* when it is `1`-tough but the
removal of any single edge destroys `1`-toughness.  For such graphs a conjecture of
Kriesell asserts a uniform minimum degree of `2`, and it is known that within
several hereditary classes (defined by a forbidden induced subgraph) minimally
`1`-tough graphs are Hamiltonian.  The class studied here is that of
`(K₁ ∪ P₄)`-free graphs: graphs with no induced subgraph isomorphic to the disjoint
union of an isolated vertex and a path on four vertices.

This file develops a self-contained account of the underlying toughness machinery
and proves the structural results that power the theory:

* `numComp_le_of_le` — the **monotonicity of the component count**: adding edges can
  only merge components.  This is the exact reduction step by which any
  Hamiltonicity-vs-toughness argument is transported from a spanning cycle to the
  ambient graph.
* `isOneTough_complete` — complete graphs are `1`-tough.
* `oneTough_two_le_degree` — every `1`-tough graph on at least three vertices has
  minimum degree at least `2` (the vertex-side heart of Kriesell's minimum-degree
  programme).
* `complete_inducedFree_of_nonAdj` / `complete_inducedFree_K1P4` — a complete graph
  forbids every induced subgraph that has a non-edge; in particular it is
  `(K₁ ∪ P₄)`-free.

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The correct atomic notion is the *component count*
  `numComp G S = |components of G − S|`.  Toughness, minimal toughness and the
  Chvátal necessary condition should all reduce to two facts about this count:
  (i) it is monotone under edge additions, and (ii) on a cycle it is bounded by
  `|S|`.  Fact (i) is graph-class independent and should be provable in full.
Experiment (Experimenter): `numComp` is realised as the cardinality of the
  connected-component type of the induced subgraph on the complement of `S`.
  The identity vertex map is a graph homomorphism `G.induce s →g H.induce s`
  whenever `G ≤ H`; the induced map on components is surjective, giving (i) via
  `Nat.card_le_card_of_surjective`.  Complete graphs have every induced subgraph
  connected, so their component count never exceeds one — hence they are `1`-tough.
  The minimum-degree theorem isolates a degree-`≤ 1` vertex `v` with neighbour `u`
  and deletes `S = {u}`: `v` becomes isolated, so `G − u` has at least two
  components while `|S| = 1`, contradicting `1`-toughness.
Analysis (Analyst): The component count is the load-bearing invariant.  Its
  monotonicity is the graph-theoretic content of "a Hamiltonian cycle certifies
  toughness"; the singleton-deletion argument is the content of "tough graphs have
  no near-pendant vertices".  Both are genuinely structural (surjections on
  quotient types, reachability from an isolated vertex), not computational.
Critique (Critic): We keep `IsOneTough` faithful (connectivity **and** the count
  inequality) rather than the vacuous count-only version, so that boundary
  witnesses such as disconnected graphs are correctly excluded.  The forbidden
  graph `K₁ ∪ P₄` is pinned down as a concrete `SimpleGraph (Fin 5)` and verified
  to have the intended non-edges, preventing a silent mis-encoding.
Synthesis (PI): Monotonicity, complete-graph toughness, the minimum-degree
  theorem, and the `(K₁ ∪ P₄)`-freeness of complete graphs assemble into a
  compact, reusable toughness toolkit; the full Hamiltonicity theorem for
  minimally `1`-tough `(K₁ ∪ P₄)`-free graphs is recorded as a future direction.
-/


open SimpleGraph Finset

open ToughP4

variable {V : Type*}

/-! ## Component count and toughness -/





/-! ## Monotonicity of the component count (the Chvátal reduction step) -/


/-! ## Complete graphs are `1`-tough -/

theorem ToughP4.numComp_complete_le_one[Fintype V] (S : Finset V) :
    numComp (⊤ : SimpleGraph V) S ≤ 1 := by sorry
