-- Prove2me | Definitions.Def_Combinatorics_BipartiteExtremalTreesFixedParts
-- name    : Combinatorics_BipartiteExtremalTreesFixedParts
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:29:12.672664+00:00
-- url     : https://prove2.me/theorems/72e4f7c5-f507-4c89-bc36-6f28d4b2d7e9
-- title:
--   Aether Catalog definitions — Combinatorics_BipartiteExtremalTreesFixedParts
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.BipartiteExtremalTreesFixedParts`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/BipartiteExtremalTreesFixedParts.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
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

namespace Catalog.Combinatorics.BipartiteExtremalTrees

open Finset Fintype SimpleGraph

/-! ### A degree characterisation of `P₄`-freeness -/



/-! ### The extremal construction: two disjoint stars -/

/-- The disjoint union of the star centred at the first left vertex (joined to all right
vertices but the first) and the star centred at the first right vertex (joined to all left
vertices but the first). -/
def twoStars (m n : ℕ) : SimpleGraph (Fin m ⊕ Fin n) where
  Adj x y := match x, y with
    | Sum.inl i, Sum.inr j => (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0)
    | Sum.inr j, Sum.inl i => (i.val = 0 ∧ j.val ≠ 0) ∨ (i.val ≠ 0 ∧ j.val = 0)
    | _, _ => False
  symm := by rintro (a | a) (b | b) h <;> exact h
  loopless := ⟨by rintro (a | a) h <;> exact h⟩

instance instDecidableAdjTwoStars (m n : ℕ) : DecidableRel (twoStars m n).Adj := by
  intro x y
  cases x <;> cases y <;> dsimp [twoStars] <;> infer_instance






/-! ### The exact fixed-part value -/






/-! ### Consistency with the decomposition theorem -/



/-! ### Hosts too small to contain the forbidden graph

When the host has fewer vertices than `T`, no copy of `T` can occur, so the extremal number
degenerates to the maximum number of edges of a bipartite graph.  This regime is what makes the
`P₄` answer `n - 1` genuinely special: it fails already for `P₅` at `n = 4`. -/

variable {W : Type*} {T : SimpleGraph W}







end Catalog.Combinatorics.BipartiteExtremalTrees


