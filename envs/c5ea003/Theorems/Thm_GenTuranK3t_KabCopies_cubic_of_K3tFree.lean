-- Prove2me | Theorems.Thm_GenTuranK3t_KabCopies_cubic_of_K3tFree
-- name    : GenTuranK3t.KabCopies_cubic_of_K3tFree
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:38:18.641075+00:00
-- url     : https://prove2.me/theorems/b4f52763-b39a-431e-9cd8-7c8973315814
-- title:
--   Cubic upper bound for the generalized Turán problem.
-- statement:
--   **Cubic upper bound for the generalized Turán problem.**  If `G` is `K_{3,t}`-free
--   then it has at most `C(t-1, b) · C(t-1, a-3) · n³` copies of `K_{a,b}`.
--
--   (The hypothesis `b + 1 ≤ t` is part of the intended statement — it is what makes the
--   bound meaningful, since otherwise `C(t-1,b) = 0` and the conclusion says the graph has
--   no copies at all — but the proof below does not need it.)
--
--   ```lean
--   theorem GenTuranK3t.KabCopies_cubic_of_K3tFree(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
--       (ha : 3 ≤ a) (hb : 3 ≤ b) (_hbt : b + 1 ≤ t) (hfree : K3tFree G t) :
--       (KabCopies G a b).card
--         ≤ ((t - 1).choose b * (t - 1).choose (a - 3)) * (Fintype.card V) ^ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Probability/GenTuranK3tUpperBound.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Probability/GenTuranK3tUpperBound.lean#L89

-- Thm stub generated from Probability/GenTuranK3tUpperBound.lean
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

theorem GenTuranK3t.KabCopies_cubic_of_K3tFree(G : SimpleGraph V) [DecidableRel G.Adj] {a b t : ℕ}
    (ha : 3 ≤ a) (hb : 3 ≤ b) (_hbt : b + 1 ≤ t) (hfree : K3tFree G t) :
    (KabCopies G a b).card
      ≤ ((t - 1).choose b * (t - 1).choose (a - 3)) * (Fintype.card V) ^ 3 := by sorry
