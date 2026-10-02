-- Prove2me | Definitions.Def_P2MAssembly_Chapter40
-- name    : P2MAssembly_Chapter40
-- status  : Definition
-- author  : @xiangyazi24
-- created : 2026-09-12T16:34:45.558555+00:00
-- url     : https://prove2.me/theorems/19c3ad82-43dd-40ef-81de-b55b2b7d5a19
-- title:
--   The friendship property and universal neighbors
-- statement:
--   For a simple undirected graph G on a finite vertex set V, Friendship(G) means that every two distinct vertices have exactly one common neighbor:
--   $$\forall v\ne w,\quad |\{u\in V:v\sim u\ \text{and}\ w\sim u\}|=1.$$
--   The requirement applies to adjacent pairs as well as nonadjacent pairs. ExistsPolitician(G) means
--   $$\exists v\in V\ \forall w\in V,\quad w\ne v\Longrightarrow v\sim w.$$
--   The latter predicate is meaningful without a finiteness assumption. The definitions do not assert nonemptiness, regularity, or the existence of a universal neighbor; those are hypotheses or conclusions of separate theorems. Both predicates are retained from Mathlib Archive.
-- source:
--   Mathlib Archive definitions, Aaron Anderson, Jalex Stark, and Kyle Miller, Apache 2.0: https://github.com/leanprover-community/mathlib4/blob/c5ea00351c28e24afc9f0f84379aa41082b1188f/Archive/Wiedijk100Theorems/FriendshipGraphs.lean#L57. The generated bundle retains the upstream author and license header; these definitions are not attributed to the importing repository.

import Init
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib

/- Original source header (imports hoisted):
/-
Copyright (c) 2020 Aaron Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aaron Anderson, Jalex Stark, Kyle Miller
-/
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
-/
/- Source module: Archive.Wiedijk100Theorems.FriendshipGraphs -/
section


/-!
# The Friendship Theorem

## Definitions and Statement
- A `Friendship` graph is one in which any two distinct vertices have exactly one neighbor in common
- A `Politician`, at least in the context of this problem, is a vertex in a graph which is adjacent
  to every other vertex.
- The friendship theorem (Erdős, Rényi, Sós 1966) states that every finite friendship graph has a
  politician.

## Proof outline
The proof revolves around the theory of adjacency matrices, although some steps could equivalently
be phrased in terms of counting walks.
- Assume `G` is a finite friendship graph.
- First we show that any two nonadjacent vertices have the same degree
- Assume for contradiction that `G` does not have a politician.
- Conclude from the last two points that `G` is `d`-regular for some `d : ℕ`.
- Show that `G` has `d ^ 2 - d + 1` vertices.
- By casework, show that if `d = 0, 1, 2`, then `G` has a politician.
- If `3 ≤ d`, let `p` be a prime factor of `d - 1`.
- If `A` is the adjacency matrix of `G` with entries in `ℤ/pℤ`, we show that `A ^ p` has trace `1`.
- This gives a contradiction, as `A` has trace `0`, and thus `A ^ p` has trace `0`.

## References
- [P. Erdős, A. Rényi, V. Sós, *On A Problem of Graph Theory*][erdosrenyisos]
- [C. Huneke, *The Friendship Theorem*][huneke2002]

-/

namespace Theorems100

noncomputable section

open Finset SimpleGraph Matrix

universe u v

variable {V : Type u} {R : Type v} [Semiring R]

section FriendshipDef

variable (G : SimpleGraph V)

open scoped Classical in
/-- This property of a graph is the hypothesis of the friendship theorem:
every pair of nonadjacent vertices has exactly one common friend,
a vertex to which both are adjacent.
-/
def Friendship [Fintype V] : Prop :=
  ∀ ⦃v w : V⦄, v ≠ w → Fintype.card (G.commonNeighbors v w) = 1

/-- A politician is a vertex that is adjacent to all other vertices.
-/
def ExistsPolitician : Prop :=
  ∃ v : V, ∀ w : V, v ≠ w → G.Adj v w

end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)





variable {R}







section Nonempty

variable [Nonempty V]







end Nonempty







variable [Nonempty V]











end Friendship



end

end Theorems100

end

/- Original source header (imports hoisted):
import Mathlib
import Archive.Wiedijk100Theorems.FriendshipGraphs
-/
/- Source module: ProofsInTheBook.Chapter40 -/
section


/-!
# Chapter 40: Of friends and politicians

From "Proofs from THE BOOK":

**Friendship theorem** (Erdős–Rényi–Sós 1966): In a finite graph where every two
distinct vertices have exactly one common neighbor, there exists a vertex adjacent
to all others (a "politician").

The book's proof uses spectral graph theory: the adjacency matrix A
satisfies A² = J + (k-1)I. The graph is d-regular; eigenvalue analysis and
a characteristic polynomial argument over 𝔽_p (for p | d-1) yields contradiction
unless d ≤ 2, which is handled separately.

Formalized in Mathlib's archive as `Theorems100.friendship_theorem`.
-/

namespace ProofsInTheBook.Chapter40

open SimpleGraph Theorems100

/-!
### Friendship theorem via Mathlib Archive

Every finite nonempty friendship graph has a politician.
-/





end ProofsInTheBook.Chapter40

end


