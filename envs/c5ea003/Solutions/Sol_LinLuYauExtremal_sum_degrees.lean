-- Prove2me | solution 1 for LinLuYauExtremal.sum_degrees
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-12T01:36:24.438436+00:00
-- url     : https://prove2.me/submissions/eb912223-38f5-4af5-b977-f1e51ce60107

-- Sol generated from Novelty/LinLuYauExtremal.lean
import Mathlib
import Definitions.Def_Novelty_LinLuYauExtremal
import Theorems.Thm_LinLuYauExtremal_nbhd_inl
import Theorems.Thm_LinLuYauExtremal_nbhd_inr
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



/-! ### Degrees and edge count -/

/-- Every matching vertex has degree `2k + 1`: one matching partner plus all of block `B`. -/
theorem degree_inl (p : Fin k) (b : Fin 2) : (H k).degree (Sum.inl (p, b)) = 2 * k + 1 := by
  rw [← card_neighborFinset_eq_degree, nbhd_inl]
  rw [Finset.card_insert_of_notMem (by simp), Finset.card_map, Finset.card_univ,
    Fintype.card_fin]

/-- Every clique vertex has degree `4k - 1`: all of block `A` plus every other clique vertex. -/
theorem degree_inr (i : Fin (2 * k)) : (H k).degree (Sum.inr i) = 4 * k - 1 := by
  rw [← card_neighborFinset_eq_degree, nbhd_inr]
  rw [Finset.card_union_of_disjoint (by
    rw [Finset.disjoint_left]
    rintro x hx hx2
    simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx hx2
    obtain ⟨a, _, rfl⟩ := hx; obtain ⟨b, _, hb⟩ := hx2; exact absurd hb (by simp))]
  simp only [Finset.card_map, Finset.card_univ, Finset.card_erase_of_mem (Finset.mem_univ _),
    Fintype.card_prod, Fintype.card_fin]
  omega



/-! ### Common neighbours (triangles through an edge) -/






/-! ### Falsification of the stated extremal count -/




open LinLuYauExtremal in
theorem solution: ∑ v : Vtx k, (H k).degree v = 12 * k ^ 2 := by
  rw [Fintype.sum_sum_type]
  have h1 : ∑ x : Fin k × Fin 2, (H k).degree (Sum.inl x) = 2 * k * (2 * k + 1) := by
    have hx : ∀ x : Fin k × Fin 2, (H k).degree (Sum.inl x) = 2 * k + 1 :=
      fun x => by obtain ⟨p, b⟩ := x; exact degree_inl p b
    rw [Finset.sum_congr rfl (fun x _ => hx x), Finset.sum_const, Finset.card_univ,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, smul_eq_mul]
    ring
  have h2 : ∑ i : Fin (2 * k), (H k).degree (Sum.inr i) = 2 * k * (4 * k - 1) := by
    rw [Finset.sum_congr rfl (fun i _ => degree_inr i), Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, smul_eq_mul]
  rw [h1, h2]
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · ring
  · obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 := ⟨k - 1, by omega⟩
    have : 4 * (n + 1) - 1 = 4 * n + 3 := by omega
    rw [this]; ring
