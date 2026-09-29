-- Prove2me | solution 1 for Catalog.Combinatorics.BipartiteExtremalTrees.mul_le_exBipParts_of_free
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T21:44:07.393217+00:00
-- url     : https://prove2.me/submissions/c3e4017e-54ab-4380-8078-bda5491cae4e

-- Sol generated from Combinatorics/BipartiteExtremalTrees.lean
import Mathlib
import Definitions.Def_Combinatorics_BipartiteExtremalTrees
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_card_edgeFinset_completeBipartiteGraph
import Theorems.Thm_Catalog_Combinatorics_BipartiteExtremalTrees_card_edgeFinset_le_exBipParts
/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # Bipartite extremal numbers of trees

This file develops the extremal theory of trees restricted to **bipartite host graphs**, in the
two variants studied in the literature:

* `exBip n T`: the maximum number of edges of a `T`-free bipartite graph on `n` vertices;
* `exBipParts m n T`: the same, when the two parts are prescribed to have sizes `m` and `n`.

## Main results

* `exBip_le_extremalNumber`: the bipartite extremal number is at most the ordinary one.
* `extremalNumber_le_two_mul_exBip`: conversely, the ordinary extremal number is at most twice
  the bipartite one (via a max-cut averaging argument), so the two functions agree up to a
  factor of two for every forbidden graph.
* `exBip_eq_sup_exBipParts`: the order-only function is the maximum of the fixed-part functions
  over all splittings `n = m + (n - m)`.
* `two_mul_exBip_starGraph_le`, `exBipParts_starGraph_le`: linear (Erdős–Sós type) upper bounds
  for stars, in both variants.
* `exBipParts_starGraph_eq`, `exBipParts_starGraph_eq_of_le`, `exBip_starGraph_eq`: exact values
  for stars with balanced parts, the extremal graph being the `k`-regular bipartite circulant
  `bipCirculant`.
* `exBipParts_starGraph`: **the complete fixed-part star formula**
  `exBipParts m n K_{1,k+1} = min (k · min m n) (m · n)` for all `m, n, k`, the extremal graph
  for unbalanced parts being the shifted interval graph `bipShift`.
* `exBip_starGraph`: **the complete order-only star formula**
  `exBip n K_{1,k+1} = min (k⌊n/2⌋) (⌊n/2⌋⌈n/2⌉)` for all `n, k`, with the two regimes
  `exBip_starGraph_of_two_mul_le` (`2k ≤ n`) and `exBip_starGraph_of_le_two_mul` (`n ≤ 2k`).
* `exBipParts_starGraph_two`, `exBip_starGraph_two`: the complete answer for `K_{1,2} = P₃`
  (`exBip n P₃ = ⌊n/2⌋` for every `n`), the extremal graph being a maximum matching.
* `free_completeBipartiteGraph_of_forall_coloring`, `mul_le_exBip_of_free`: the general
  colouring criterion producing the natural linear lower-bound construction `K_{a,b}`.
* `coloring_unique_of_connected`, `exBip_ge_of_connected`, `exBipParts_eq_mul_of_connected`:
  for a *connected* forbidden graph `T` the colour classes are an invariant, giving the general
  lower bound `s (n - s) ≤ exBip n T` whenever both classes exceed `s`, and the *exact* value
  `exBipParts m n T = m n` whenever both classes exceed `m`.
* `exBip_pathGraph_lower_bound`: the resulting lower bound `(⌊p/2⌋-1)(n-⌊p/2⌋+1)` for paths.
* `exBip_pathGraph_four`: the exact value `exBip n P₄ = n - 1` for `n ≥ 2`.

## Lab notes (exhaustive search, all labelled graphs on `n ≤ 7` vertices)

```
n        2  3  4  5  6  7
P₄       1  2  3  4  5  6      = n - 1        (proved: exBip_pathGraph_four)
P₅       1  2  4  4  5  6      ≠ n - 1 for n = 4 and, by disjoint C₄'s, for n = 8
K_{1,2}  1  1  2  2  3  3      = ⌊n/2⌋        (proved: exBip_starGraph_two)
K_{1,3}  1  2  4  4  6  6      = 2N at n = 2N (proved: exBip_starGraph_eq, k = 2 ≤ N)
```

The entry `K_{1,3}` at `n = 5` is `4`, strictly below `⌊k·n/2⌋ = 5`: the odd-order star problem
has a genuine parity obstruction.  `exBip_starGraph` explains and resolves it: the true value is
`min (k⌊n/2⌋) (⌊n/2⌋⌈n/2⌉)`, which for `n = 5, k = 2` is `min 4 6 = 4`, and which reproduces the
whole `K_{1,2}` and `K_{1,3}` rows above.  See `ComputationalEvidence.md` for details.
-/

open Catalog.Combinatorics.BipartiteExtremalTrees

open Finset Fintype SimpleGraph





variable {W : Type*} {T : SimpleGraph W}







/-! ### Max-cut: the ordinary extremal number is at most twice the bipartite one

Deleting the edges inside the two sides of a maximum cut of a `T`-free graph leaves a *bipartite*
`T`-free graph with at least half of the edges.  Hence the bipartite restriction of the
Erdős–Sós problem loses at most a factor of two:
`exBip n T ≤ extremalNumber n T ≤ 2 * exBip n T`. -/










/-! ### The complete bipartite host -/




/-! ### Basic API for the fixed-part bipartite extremal number -/






/-! ### Stars

The star `K_{1,k}` is the first family for which the bipartite extremal number can be computed
exactly. -/






/-! ### The bipartite circulant, and exact star values

`bipCirculant N k` is the `k`-regular bipartite graph on parts `Fin N`, `Fin N` in which
`inl i` is joined to `inr j` exactly when `j - i` is one of the `k` smallest residues.
It is the extremal construction for stars. -/












/-! ### The shifted construction and the general fixed-part star formula

For unbalanced parts the circulant is replaced by the *shifted interval* graph `bipShift`:
with `m ≤ n`, the left vertex `i` is joined to the `k` right vertices `i, i+1, …, i+k-1`
(indices modulo `n`).  Its left degrees are exactly `k` and its right degrees are at most `k`,
so it is `K_{1,k+1}`-free with `k * m` edges, matching the upper bound `k * min m n`. -/










/-! ### Matchings: the complete answer for `P₃ = K_{1,2}`

A `K_{1,2}`-free graph is a matching, and the perfect matching between the two parts is
extremal. -/








/-! ### Lower bounds from the bipartition of `T`

If every proper `2`-colouring of `T` has both colour classes large, then the complete bipartite
graph with a small side is `T`-free, giving the natural linear lower-bound construction. -/




/-! ### Paths

The path on `p` vertices has colour classes of sizes `⌈p/2⌉` and `⌊p/2⌋`; consequently
`K_{⌊p/2⌋-1, n-⌊p/2⌋+1}` is `P_p`-free. -/

/-! ### Connected forbidden graphs: the general lower-bound construction

For a connected `T` the proper two-colouring is unique up to swapping the two colours, so the
sizes of the colour classes are an invariant of `T`.  If both classes have more than `s`
vertices then no complete bipartite graph with a part of size `s` can contain `T`; this is the
natural lower-bound construction of the bipartite Erdős–Sós problem, and in the fixed-part
setting it is even *optimal*. -/














/-! ### Relating the two extremal functions

The order-only bipartite extremal number is the maximum of the fixed-part ones over all
splittings of `n`. -/



/-! ### The complete order-only star formula

Combining the fixed-part formula `exBipParts_starGraph` with the decomposition
`exBip_eq_sup_exBipParts` solves the order-only star problem for *all* orders `n` and all `k`,
including the odd orders where the naive bound `⌊k n / 2⌋` is not attained. -/






/-! ### The exact bipartite extremal number of `P₄`

A bipartite `P₄`-free graph is a disjoint union of stars; we prove the resulting sharp bound
`exBip n P₄ = n - 1` for `n ≥ 2` by a degree argument. -/








open Catalog.Combinatorics.BipartiteExtremalTrees in
theorem solution{a b : ℕ}
    (h : T.Free (completeBipartiteGraph (Fin a) (Fin b))) : a * b ≤ exBipParts a b T := by
  have hcopy := card_edgeFinset_le_exBipParts (G := completeBipartiteGraph (Fin a) (Fin b)) h le_rfl
  rwa [card_edgeFinset_completeBipartiteGraph] at hcopy
