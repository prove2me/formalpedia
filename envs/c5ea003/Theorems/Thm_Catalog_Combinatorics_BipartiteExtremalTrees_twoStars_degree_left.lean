-- Prove2me | Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_twoStars_degree_left
-- name    : Catalog.Combinatorics.BipartiteExtremalTrees.twoStars_degree_left
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:00:26.891722+00:00
-- url     : https://prove2.me/theorems/99a203cc-02d5-494d-b7b4-c368324997aa
-- title:
--   TwoStars degree left
-- statement:
--   Formal statement of `Catalog.Combinatorics.BipartiteExtremalTrees.twoStars_degree_left` from the Aether Catalog (Combinatorics). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem Catalog.Combinatorics.BipartiteExtremalTrees.twoStars_degree_left{m n : ℕ} (hn : 0 < n) (i : Fin m) :
--       (twoStars m n).degree (Sum.inl i) = if i.val = 0 then n - 1 else 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/BipartiteExtremalTreesFixedParts.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/BipartiteExtremalTreesFixedParts.lean#L90

-- Thm stub generated from Combinatorics/BipartiteExtremalTreesFixedParts.lean
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

theorem Catalog.Combinatorics.BipartiteExtremalTrees.twoStars_degree_left{m n : ℕ} (hn : 0 < n) (i : Fin m) :
    (twoStars m n).degree (Sum.inl i) = if i.val = 0 then n - 1 else 1 := by sorry
