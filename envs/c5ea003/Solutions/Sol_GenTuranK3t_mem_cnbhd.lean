-- Prove2me | solution 1 for GenTuranK3t.mem_cnbhd
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T04:18:20.989592+00:00
-- url     : https://prove2.me/submissions/71c1210c-644b-4a62-8779-391668995484

-- Sol generated from Probability/GenTuranK3tUpperBound.lean
import Mathlib
import Definitions.Def_Probability_GenTuranK3tUpperBound
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

open GenTuranK3t

variable {V : Type*} [Fintype V] [DecidableEq V]













open GenTuranK3t in
@[simp] theorem solution{G : SimpleGraph V} [DecidableRel G.Adj] {S : Finset V} {w : V} :
    w ∈ cnbhd G S ↔ ∀ u ∈ S, G.Adj u w := by
  simp [cnbhd]
