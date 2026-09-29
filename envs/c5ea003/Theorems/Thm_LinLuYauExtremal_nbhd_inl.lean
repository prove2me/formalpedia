-- Prove2me | Theorems.Thm_LinLuYauExtremal_nbhd_inl
-- name    : LinLuYauExtremal.nbhd_inl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T16:06:34.444452+00:00
-- url     : https://prove2.me/theorems/95a6f7f7-51eb-405c-8518-8389a78b77de
-- title:
--   A matching (block-`A`) vertex is adjacent to its unique matching partner and to all of
-- statement:
--   A matching (block-`A`) vertex is adjacent to its unique matching partner and to all of
--   block `B`.
--
--   ```lean
--   theorem LinLuYauExtremal.nbhd_inl(p : Fin k) (b : Fin 2) :
--       (H k).neighborFinset (Sum.inl (p, b)) =
--         insert (Sum.inl (p, b + 1)) (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Novelty/LinLuYauExtremal.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Novelty/LinLuYauExtremal.lean#L116

-- Thm stub generated from Novelty/LinLuYauExtremal.lean
import Mathlib
import Definitions.Def_Novelty_LinLuYauExtremal
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The matching–clique join: local structure of a curvature extremal candidate

Discrete Ollivier–Lin–Lu–Yau (LLY) Ricci curvature of an edge `x ~ y` in a graph is
governed by two purely local quantities: the degrees `d(x), d(y)` and the number of
common neighbours `#(x,y) = |N(x) ∩ N(y)|` (the count of triangles through the edge).
Edges with small common neighbourhood relative to their endpoints' degrees are the ones
that carry non-positive curvature.

This file studies the *balanced matching–clique join* `H(k)`, proposed as the extremal
graph on `n = 4k` vertices for the problem "how many edges can a graph have while still
containing an edge of non-positive curvature?".  The construction partitions the vertex
set into two blocks of equal size `2k`:

* block `A` (`Sum.inl`) induces a **perfect matching** (`k` disjoint edges);
* block `B` (`Sum.inr`) induces a **complete graph** `K_{2k}`;
* every `A`–`B` pair is joined (complete bipartite between the blocks).

We compute the entire local profile of this graph exactly:

* the degree of every vertex (`degree_inl`, `degree_inr`);
* the total number of edges (`card_edgeFinset`), via the handshake identity;
* the common-neighbour count of every edge, split by type
  (`common_matching`, `common_clique`, `common_join`);
* the structural signature that the **matching edges are locally sparsest**
  (`matching_locally_sparsest`), the combinatorial fingerprint of the
  curvature-minimising edge.

## Catalog connections
* `math.CO 05C35 - Extremal problems for graphs`: `card_edgeFinset` pins down the exact
  edge count of the proposed extremal family, and `edges_ne_claimed_threshold` shows this
  count is *not* the conjectured threshold `T(n)` — a genuine falsification, see Lab Notes.
* `math.DG 53C21 - Curves and surfaces`: the common-neighbour profile
  (`common_matching`, `common_clique`, `common_join`) is exactly the discrete Ricci input
  that decides the sign of Lin–Lu–Yau curvature on each edge class.
* `math.CO 05C05 - Graph connectivity`: `construction_requires_div_four` records the parity
  obstruction (a perfect matching on `n/2` vertices forces `4 ∣ n`).

-- !-- Lab Notes -- !--
Hypothesis (Hypothesizer): The balanced matching–clique join on `n` vertices is the unique
  edge-maximiser among graphs possessing an edge of non-positive LLY curvature, with edge
  count `T(n) = (n²-3n)/2 - ⌈n/2⌉ + 2`.
Experiment (Experimenter): We built `H(k)` concretely on `(Fin k × Fin 2) ⊕ Fin (2k)`,
  computed every degree, and summed via the handshake lemma to get `|E| = 6k²`.  With
  `n = 4k` this is `3n²/8`.  We then computed the common-neighbour count of every edge:
  matching edges see `2k` triangles, join edges `2k`, clique edges `4k-2`.
Analysis (Analyst): TWO things fail in the stated conjecture.  (1) The edge count is
  `3n²/8`, whereas the claimed `T(n)` equals `(n-2)²/2`; these are unequal for every
  admissible `n` (`edges_ne_claimed_threshold`).  Since `(n-2)²/2 = C(n,2) - (3n-4)/2`
  removes only `Θ(n)` edges from the complete graph, the *true* maximiser must be
  near-complete, missing only linearly many edges — the opposite of the sparse
  matching–clique join, which is missing `Θ(n²)` edges.  (2) A perfect matching on `n/2`
  vertices needs `n/2` even, i.e. `4 ∣ n`; the family does not even exist for `n ≡ 2 (4)`.
Critique (Critic): The salvageable, fully rigorous core is the *local profile* of `H(k)`:
  the matching edges are strictly locally sparsest for `k ≥ 2` (`matching_locally_sparsest`),
  which is the correct combinatorial reason those edges minimise curvature.  Every theorem
  here is a genuine cardinality or inequality — none is vacuous or definitional.
Synthesis (PI): `H(k)` is a clean, exactly-computable testbed whose local geometry we now
  understand completely; the extremal *count* conjecture is refuted and redirected toward
  near-complete graphs in FUTURE_DIRECTIONS.
-/

open SimpleGraph Finset

open LinLuYauExtremal






variable {k : ℕ}

/-! ### Adjacency by block -/





/-! ### Neighbourhoods -/

theorem LinLuYauExtremal.nbhd_inl(p : Fin k) (b : Fin 2) :
    (H k).neighborFinset (Sum.inl (p, b)) =
      insert (Sum.inl (p, b + 1)) (Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) := by sorry
