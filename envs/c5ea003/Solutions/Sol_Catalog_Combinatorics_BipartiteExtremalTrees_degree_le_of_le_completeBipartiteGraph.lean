-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.degree_le_of_le_completeBipartiteGraph
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:39:10.50698+00:00
-- url     : https://prove2.me/submissions/972bbb38-8c0a-4b61-a930-017df43be5ae

-- Sol generated from Combinatorics/BipartiteExtremalTreesFixedParts.lean
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
import Definitions.Def_Combinatorics_BipartiteExtremalTreesFixedParts
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The fixed-part bipartite extremal number of `P₄`

This file continues `Catalog/Combinatorics/BipartiteExtremalTrees.lean`, where the order-only
value `exBip n P₄ = n - 1` (`exBip_pathGraph_four`) was determined.  Here we settle the
**fixed-part** problem for `P₄` completely:

* `pathGraph_four_free_iff_forall_degree_one`: a graph is `P₄`-free **iff** every edge has an
  endpoint of degree one.  (The `→` direction of the bipartite version was
  `exists_degree_one_endpoint`; the `←` direction, proved here, needs no bipartiteness and is
  what turns the criterion into a tool for building extremal graphs.)
* `twoStars`: the disjoint union of a star centred in the left part and a star centred in the
  right part, the extremal construction.
* `exBipParts_pathGraph_four`: `exBipParts m n P₄ = m + n - 2` whenever `2 ≤ m` and `2 ≤ n`.
* `exBipParts_pathGraph_four_formula`: the complete answer for all `m, n`, namely
  `exBipParts m n P₄ = if min m n ≤ 1 then m * n else m + n - 2`.
* `exBip_pathGraph_four_eq_sup`: consistency with the decomposition theorem — maximising
  `m + (n - m) - 2` over the splittings of `n` returns exactly `n - 1`, the order-only value,
  the maximum being attained at the *unbalanced* splitting `m = 1`.

The last point is a genuinely informative phenomenon: for `P₄` the fixed-part optimum
`m + n - 2` is *smaller* than the order-only optimum for every balanced splitting, and the
order-only extremal graph is forced to be maximally unbalanced (a single star).
-/

open Catalog.Combinatorics.BipartiteExtremalTrees

open Finset Fintype SimpleGraph

/-! ### A degree characterisation of `P₄`-freeness -/



/-! ### The extremal construction: two disjoint stars -/








/-! ### The exact fixed-part value -/






/-! ### Consistency with the decomposition theorem -/



/-! ### Hosts too small to contain the forbidden graph

When the host has fewer vertices than `T`, no copy of `T` can occur, so the extremal number
degenerates to the maximum number of edges of a bipartite graph.  This regime is what makes the
`P₄` answer `n - 1` genuinely special: it fails already for `P₅` at `n = 4`. -/

variable {W : Type*} {T : SimpleGraph W}








open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution{m n : ℕ} {G : SimpleGraph (Fin m ⊕ Fin n)}
    [DecidableRel G.Adj] (hsub : G ≤ completeBipartiteGraph (Fin m) (Fin n)) :
    ∀ v, G.degree v ≤ max m n := by
  classical
  rintro (i | j)
  · rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card (t := Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩) ?_)
      (by simp)
    rintro (x | x) hx
    · have := hsub ((mem_neighborFinset ..).mp hx)
      simp [completeBipartiteGraph] at this
    · simp
  · rw [← card_neighborFinset_eq_degree]
    refine le_trans (Finset.card_le_card (t := Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩) ?_)
      (by simp)
    rintro (x | x) hx
    · simp
    · have := hsub ((mem_neighborFinset ..).mp hx)
      simp [completeBipartiteGraph] at this
