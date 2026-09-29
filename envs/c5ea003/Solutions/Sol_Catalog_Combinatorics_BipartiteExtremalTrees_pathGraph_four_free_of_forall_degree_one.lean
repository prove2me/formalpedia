-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.pathGraph_four_free_of_forall_degree_one
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T22:05:41.612783+00:00
-- url     : https://prove2.me/submissions/debbf887-b067-4e2d-9eca-6b288c58a456

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
theorem solution{V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj]
    (h : ∀ {u v : V}, G.Adj u v → G.degree u = 1 ∨ G.degree v = 1) :
    (pathGraph 4).Free G := by
  rintro ⟨f⟩
  have hadj : ∀ {a b : Fin 4}, (pathGraph 4).Adj a b → G.Adj (f a) (f b) := fun hab =>
    f.toHom.map_adj hab
  have h01 : (pathGraph 4).Adj 0 1 := by simp [pathGraph_adj]
  have h12 : (pathGraph 4).Adj 1 2 := by simp [pathGraph_adj]
  have h23 : (pathGraph 4).Adj 2 3 := by simp [pathGraph_adj]
  -- the two middle vertices of the path both have degree at least two in `G`
  have key : ∀ {a b c : Fin 4}, (pathGraph 4).Adj a b → (pathGraph 4).Adj b c → a ≠ c →
      2 ≤ G.degree (f b) := by
    intro a b c hab hbc hac
    rw [← card_neighborFinset_eq_degree]
    refine Finset.one_lt_card.mpr ⟨f a, ?_, f c, ?_, ?_⟩
    · exact (mem_neighborFinset ..).mpr (hadj hab).symm
    · exact (mem_neighborFinset ..).mpr (hadj hbc)
    · exact fun hcon => hac (f.injective hcon)
  have hd1 : 2 ≤ G.degree (f 1) := key h01 h12 (by decide)
  have hd2 : 2 ≤ G.degree (f 2) := key h12 h23 (by decide)
  rcases h (hadj h12) with hc | hc <;> omega
