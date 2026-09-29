-- Prove2me | Definitions.Def_Probability_GenTuranK3tUpperBound
-- name    : Probability_GenTuranK3tUpperBound
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:17:13.61289+00:00
-- url     : https://prove2.me/theorems/6348bb25-56a9-48f3-8409-9439c715d9fa
-- title:
--   Aether Catalog definitions — Probability_GenTuranK3tUpperBound
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.GenTuranK3tUpperBound`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/GenTuranK3tUpperBound.lean by skeleton subtraction
import Mathlib
/-
Copyright (c) 2026 Harmonic. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# A cubic upper bound for the generalized Turán problem `ex(n, K_{a,b}, K_{3,t})`

For a host graph `G` on `n` vertices which contains no complete bipartite subgraph
`K_{3,t}` — equivalently, in which every three vertices have at most `t - 1` common
neighbours — the number of copies of `K_{a,b}` (`a, b ≥ 3`) is `O(n³)`, with an explicit
constant depending only on `a`, `b` and `t`:

`#K_{a,b}-copies ≤ C(t-1, b) · C(t-1, a-3) · n³`.

The proof is a two-step fibred double count.  A copy is a pair `(A, B)` of vertex sets,
`|A| = a`, `|B| = b`, complete to each other.

* Choose three vertices `T ⊆ A`.  There are at most `C(n,3) ≤ n³` possibilities.
* Since every vertex of `B` is a common neighbour of `T`, `B` is a `b`-subset of
  `cnbhd G T`, a set of size `≤ t - 1` by `K_{3,t}`-freeness: `≤ C(t-1, b)` possibilities.
* Symmetrically, every vertex of `A \ T` is a common neighbour of `B`, and `B` itself
  contains a triple, so `cnbhd G B` also has size `≤ t - 1`: `≤ C(t-1, a-3)` possibilities.

The bound follows because a copy is reconstructed from `(T, B, A \ T)`.

The downward closure of this bound under the subgraph order is
`Probability.GenTuranK3tDownwardClosure`.
-/

open Finset

namespace GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The common neighbourhood of a vertex set `S`: the vertices adjacent to *every*
element of `S`. -/
def cnbhd (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) : Finset V :=
  univ.filter fun w => ∀ u ∈ S, G.Adj u w



/-- `G` is `K_{3,t}`-free: no three vertices have `t` common neighbours. -/
def K3tFree (G : SimpleGraph V) [DecidableRel G.Adj] (t : ℕ) : Prop :=
  ∀ S : Finset V, S.card = 3 → (cnbhd G S).card < t

/-- The copies of `K_{a,b}` in `G`: pairs `(A, B)` of vertex sets of sizes `a` and `b`
that are completely joined to each other. -/
def KabCopies (G : SimpleGraph V) [DecidableRel G.Adj] (a b : ℕ) :
    Finset (Finset V × Finset V) :=
  univ.filter fun P => P.1.card = a ∧ P.2.card = b ∧ ∀ u ∈ P.1, ∀ v ∈ P.2, G.Adj u v


/-- A choice of three vertices inside a set of size at least three. -/
noncomputable def triple (A : Finset V) : Finset V :=
  if h : 3 ≤ A.card then (Finset.exists_subset_card_eq h).choose else ∅





end GenTuranK3t


