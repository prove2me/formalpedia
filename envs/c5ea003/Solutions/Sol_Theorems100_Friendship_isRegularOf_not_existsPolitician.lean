-- Prove2me | solution 1 for Theorems100.Friendship.isRegularOf_not_existsPolitician
-- status  : ACCEPTED   (prove)
-- author  : @xiangyazi24
-- created : 2026-09-12T16:45:02.221855+00:00
-- url     : https://prove2.me/submissions/600a2c4b-1dea-4dc7-9def-d1b80efc0752

import Init
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.LinearAlgebra.Matrix.Charpoly.FiniteField
import Mathlib
import Definitions.Def_P2MAssembly_Chapter40


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





end FriendshipDef

variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)

namespace Friendship

variable (R)

set_option backward.isDefEq.respectTransparency false in
open scoped Classical in
include hG in
/-- One characterization of a friendship graph is that there is exactly one walk of length 2
  between distinct vertices. These walks are counted in off-diagonal entries of the square of
  the adjacency matrix, so for a friendship graph, those entries are all 1. -/
theorem adjMatrix_sq_of_ne {v w : V} (hvw : v ≠ w) :
    (G.adjMatrix R ^ 2 : Matrix V V R) v w = 1 := by
  rw [sq, ← Nat.cast_one, ← hG hvw]
  simp only [mul_adjMatrix_apply, neighborFinset_eq_filter, adjMatrix_apply,
    sum_boole, filter_filter, and_comm, commonNeighbors,
    Fintype.card_ofFinset (s := filter (fun x ↦ x ∈ G.neighborSet v ∩ G.neighborSet w) univ),
    Set.mem_inter_iff, mem_neighborSet]

open scoped Classical in
include hG in
/-- This calculation amounts to counting the number of length 3 walks between nonadjacent vertices.
  We use it to show that nonadjacent vertices have equal degrees. -/
theorem adjMatrix_pow_three_of_not_adj {v w : V} (non_adj : ¬G.Adj v w) :
    (G.adjMatrix R ^ 3 : Matrix V V R) v w = degree G v := by
  rw [pow_succ', adjMatrix_mul_apply, degree, card_eq_sum_ones, Nat.cast_sum]
  apply sum_congr rfl
  intro x hx
  rw [adjMatrix_sq_of_ne _ hG, Nat.cast_one]
  rintro ⟨rfl⟩
  rw [mem_neighborFinset] at hx
  exact non_adj hx

variable {R}

open scoped Classical in
include hG in
/-- As `v` and `w` not being adjacent implies
  `degree G v = ((G.adjMatrix R) ^ 3) v w` and `degree G w = ((G.adjMatrix R) ^ 3) v w`,
  the degrees are equal if `((G.adjMatrix R) ^ 3) v w = ((G.adjMatrix R) ^ 3) w v`

  This is true as the adjacency matrix is symmetric. -/
theorem degree_eq_of_not_adj {v w : V} (hvw : ¬G.Adj v w) : degree G v = degree G w := by
  rw [← Nat.cast_id (G.degree v), ← Nat.cast_id (G.degree w),
    ← adjMatrix_pow_three_of_not_adj ℕ hG hvw,
    ← adjMatrix_pow_three_of_not_adj ℕ hG fun h => hvw (G.symm h)]
  conv_lhs => rw [← transpose_adjMatrix]
  simp only [pow_succ _ 2, sq, ← transpose_mul, transpose_apply]
  simp only [mul_assoc]





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


open Theorems100
open Finset SimpleGraph Matrix
universe u v
variable {V : Type u} {R : Type v} [Semiring R]
variable [Fintype V] {G : SimpleGraph V} {d : ℕ} (hG : Friendship G)
open Theorems100.Friendship
variable (R)
variable {R}
variable [Nonempty V]
open scoped Classical
include hG

theorem solution (hG' : ¬ExistsPolitician G) :
    ∃ d : ℕ, G.IsRegularOfDegree d := by
  have v := Classical.arbitrary V
  use G.degree v
  intro x
  by_cases hvx : G.Adj v x; swap; · exact (degree_eq_of_not_adj hG hvx).symm
  dsimp only [Theorems100.ExistsPolitician] at hG'
  push Not at hG'
  rcases hG' v with ⟨w, hvw', hvw⟩
  rcases hG' x with ⟨y, hxy', hxy⟩
  by_cases hxw : G.Adj x w
  swap; · rw [degree_eq_of_not_adj hG hvw]; exact degree_eq_of_not_adj hG hxw
  rw [degree_eq_of_not_adj hG hxy]
  by_cases hvy : G.Adj v y
  swap; · exact (degree_eq_of_not_adj hG hvy).symm
  rw [degree_eq_of_not_adj hG hvw]
  apply degree_eq_of_not_adj hG
  intro hcontra
  rcases Finset.card_eq_one.mp (hG hvw') with ⟨⟨a, ha⟩, h⟩
  have key : ∀ {x}, x ∈ G.commonNeighbors v w → x = a := by
    intro x hx
    have h' : ⟨x, hx⟩ ∈ (univ : Finset (G.commonNeighbors v w)) := mem_univ (Subtype.mk x hx)
    rw [h, mem_singleton] at h'
    injection h'
  apply hxy'
  rw [key ((mem_commonNeighbors G).mpr ⟨hvx, G.symm hxw⟩),
    key ((mem_commonNeighbors G).mpr ⟨hvy, G.symm hcontra⟩)]
