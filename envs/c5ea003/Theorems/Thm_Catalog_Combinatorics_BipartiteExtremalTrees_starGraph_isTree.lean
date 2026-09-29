-- Prove2me | Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_starGraph_isTree
-- name    : Catalog.Combinatorics.BipartiteExtremalTrees.starGraph_isTree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T21:02:28.921591+00:00
-- url     : https://prove2.me/theorems/abc85ead-bf86-4eab-bae3-3054108cd240
-- title:
--   The star `K_{1,k}` is a tree.
-- statement:
--   **The star `K_{1,k}` is a tree.**
--
--   ```lean
--   theorem Catalog.Combinatorics.BipartiteExtremalTrees.starGraph_isTree(k : ℕ) : (starGraph k).IsTree := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Combinatorics/BipartiteExtremalTreesErdosSos.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Combinatorics/BipartiteExtremalTreesErdosSos.lean#L270

-- Thm stub generated from Combinatorics/BipartiteExtremalTreesErdosSos.lean
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
import Definitions.Def_Combinatorics_BipartiteExtremalTreesFixedParts
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A linear Erdős–Sós type upper bound for *every* tree, bipartite and not

This file settles, up to a factor of two in the slope, Conjecture 2 of the research thread
started in `Catalog/Combinatorics/BipartiteExtremalTrees.lean`: the bipartite extremal number of
a tree is linear in the order of the host, with a slope depending only on the tree.

The engine is the classical *greedy embedding lemma*, formalised here in full:

* `tree_isContained_of_forall_le_degree`: **every** graph whose minimum degree is at least the
  number of edges of a tree `T` contains a copy of `T`.  The proof is an induction on the order
  of `T` in which a leaf is removed (`SimpleGraph.IsTree.exists_vert_degree_one_of_nontrivial`),
  the smaller tree is embedded by the inductive hypothesis, and the leaf is placed on a neighbour
  of the image of its parent that has not been used yet — such a neighbour exists precisely
  because the degree bound exceeds the number of already embedded vertices.

Its consequences, obtained by deleting a vertex of small degree and inducting on the order of the
host (so that a `T`-free graph is exhibited as `(k-1)`-degenerate):

* `exists_degree_le_of_isTree_free`: a `T`-free graph has a vertex of degree at most `k - 1`.
* `card_edgeFinset_le_of_isTree_free`: a `T`-free graph on `N` vertices has at most `(k-1)·N`
  edges, `k` being the number of edges of the tree `T`.
* `exBip_le_of_isTree`, `exBipParts_le_of_isTree`, `extremalNumber_le_of_isTree`: the same bound
  for the three extremal functions, i.e. **a linear bipartite Erdős–Sós bound for all trees**.
* `two_mul_exBip_le_of_isTree`: the bound in the normalisation of the Erdős–Sós conjecture,
  `2·exBip n T ≤ 2(k-1)·n`, so the conjectural slope `k-1` is missed by at most a factor of two.

Two families are then fed into the general theorem.

* `starGraph_isTree` and `star_greedy_bound_factor_two_sharp`: for stars the greedy bound is
  *exactly* a factor two off the truth `exBip n K_{1,k+1} = k⌊n/2⌋`, so no strengthening of the
  degeneracy argument alone can beat the factor two in general.
* `pathGraph_isAcyclic`, `pathGraph_isTree` (the acyclicity proof — a bridge/side-invariant
  argument — appears to be missing from Mathlib) and `exBip_pathGraph_bounds`:
  `(⌊p/2⌋-1)(n-⌊p/2⌋+1) ≤ exBip n P_p ≤ (p-2)·n`, sandwiching the bipartite extremal number of
  every path between two explicit linear functions of `n`.  For `p = 4` the two sides are
  `n - 1` and `2n`, and the exact answer `n - 1` (`exBip_pathGraph_four`) sits at the lower end.
-/

open Catalog.Combinatorics.BipartiteExtremalTrees

open Finset Fintype SimpleGraph

universe u v

/-! ### The greedy embedding lemma -/




/-! ### The linear upper bound -/







/-! ### Stars: the greedy bound is off by exactly a factor of two -/

theorem Catalog.Combinatorics.BipartiteExtremalTrees.starGraph_isTree(k : ℕ) : (starGraph k).IsTree := by sorry
