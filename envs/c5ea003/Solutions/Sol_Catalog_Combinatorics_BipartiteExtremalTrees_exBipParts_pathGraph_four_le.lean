-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.exBipParts_pathGraph_four_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:52:58.646841+00:00
-- url     : https://prove2.me/submissions/846bd957-6f5c-4fd6-9c44-12f7ed6c6064

-- Sol generated from Combinatorics/BipartiteExtremalTreesFixedParts.lean
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
import Definitions.Def_Combinatorics_BipartiteExtremalTreesFixedParts
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_card_edgeFinset_le_card_degree_one
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_degree_le_of_le_completeBipartiteGraph
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_exBipParts_le_iff
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_exists_degree_one_endpoint
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


/-- A graph contained in `K_{m,n}` is bipartite. -/
theorem isBipartite_of_le_completeBipartiteGraph {m n : ℕ} {G : SimpleGraph (Fin m ⊕ Fin n)}
    (hsub : G ≤ completeBipartiteGraph (Fin m) (Fin n)) : G.IsBipartite := by
  refine ⟨⟨Sum.elim (fun _ => (0 : Fin 2)) (fun _ => (1 : Fin 2)), ?_⟩⟩
  rintro (a | a) (b | b) hadj <;> have := hsub hadj <;>
    simp_all [completeBipartiteGraph]




/-! ### Consistency with the decomposition theorem -/



/-! ### Hosts too small to contain the forbidden graph

When the host has fewer vertices than `T`, no copy of `T` can occur, so the extremal number
degenerates to the maximum number of edges of a bipartite graph.  This regime is what makes the
`P₄` answer `n - 1` genuinely special: it fails already for `P₅` at `n = 4`. -/

variable {W : Type*} {T : SimpleGraph W}








open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution{m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) :
    exBipParts m n (pathGraph 4) ≤ m + n - 2 := by
  classical
  rw [exBipParts_le_iff]
  intro G hfree hsub
  have hbip := isBipartite_of_le_completeBipartiteGraph hsub
  have hdegbd : ∀ v, G.degree v ≤ m + n - 2 := fun v =>
    le_trans (degree_le_of_le_completeBipartiteGraph hsub v) (by omega)
  have hedge : ∀ {u v}, G.Adj u v → G.degree u = 1 ∨ G.degree v = 1 := fun huv =>
    exists_degree_one_endpoint hbip hfree huv
  have hcard := card_edgeFinset_le_card_degree_one hedge
  set D := univ.filter (fun v : Fin m ⊕ Fin n => G.degree v = 1) with hD
  set Dc := univ.filter (fun v : Fin m ⊕ Fin n => ¬ G.degree v = 1) with hDc
  have hsplit : #D + #Dc = m + n := by
    rw [hD, hDc, Finset.card_filter_add_card_filter_not]
    simp
  have hsum : ∑ v : Fin m ⊕ Fin n, G.degree v = 2 * #G.edgeFinset :=
    SimpleGraph.sum_degrees_eq_twice_card_edges G
  have hsum2 : ∑ v ∈ D, G.degree v + ∑ v ∈ Dc, G.degree v = 2 * #G.edgeFinset := by
    rw [← hsum, hD, hDc]
    exact Finset.sum_filter_add_sum_filter_not _ _ _
  have hsumD : ∑ v ∈ D, G.degree v = #D := by
    rw [Finset.sum_congr rfl (fun v hv => (Finset.mem_filter.mp hv).2), Finset.sum_const,
      smul_eq_mul, mul_one]
  rcases Nat.lt_or_ge (#Dc) 2 with hlt | hge
  · -- few exceptional vertices: use the degree sum
    have hbound : ∑ v ∈ Dc, G.degree v ≤ #Dc * (m + n - 2) := by
      simpa [smul_eq_mul] using Finset.sum_le_card_nsmul Dc _ (m + n - 2) fun v _ => hdegbd v
    interval_cases h : #Dc
    · simp only [Nat.zero_mul, Nat.le_zero] at hbound
      omega
    · rw [Nat.one_mul] at hbound
      omega
  · omega
