-- Prove2me | Definitions.Def_ProofsInTheBook_Chapter34
-- name    : ProofsInTheBook_Chapter34
-- status  : Definition
-- author  : @Xiang Huang
-- created : 2026-09-12T15:57:15.250982+00:00
-- url     : https://prove2.me/theorems/a77158aa-b2dc-4a5d-b5be-2fbaecf5a159
-- title:
--   Dinitz arrays, directed kernels, and list colorings
-- statement:
--   An order-$n$ array has cells $\operatorname{Fin}(n)^2$. Distinct cells conflict exactly when they share a row or column. Given finite color lists $L_{ij}$, a Dinitz solution chooses $c(i,j)\in L_{ij}$ and gives different colors to conflicting cells. The cyclic value of cell $(i,j)$ is $i+j$ in $\operatorname{Fin}(n)$. The directed relation sends row-conflicts toward larger cyclic values and column-conflicts toward smaller cyclic values.
--
--   For a finite vertex set $S$, an adjacency relation and a directed relation, a kernel is a subset $K\subseteq S$ with no adjacent distinct members such that every vertex of $S\setminus K$ has an outgoing edge to $K$. Kernel-perfectness requires a kernel in every nonempty induced finite subset. A matching of array cells contains no two conflicting cells; the encoded stable matching additionally requires each unmatched cell in the given domain to have an outgoing edge to a matched cell. The bundle also defines out-neighbors and proper list colorings restricted to a finite domain.
-- source:
--   Martin Aigner and Günter M. Ziegler, Proofs from THE BOOK, 6th edition, Springer, 2018, Chapter 38, “The Dinitz problem”, pp. 271–276 (https://doi.org/10.1007/978-3-662-57265-8_38). Original definition source: https://github.com/xiangyazi24/proof_in_the_book/blob/88d88d141768cded75e782c525ef1bf04b8fe220/ProofsInTheBook/Chapter34.lean#L19. The generated bundle retains definitions and supporting declarations from this source; the book citation identifies their topic rather than asserting that each auxiliary structure appears in the book.

import Mathlib

/-!
# Chapter 34: The Dinitz problem

From "Proofs from THE BOOK":

**Galvin's theorem** (solving the Dinitz conjecture): For any assignment
of n-element color lists to the n² cells of an n×n array, there exists
a proper Latin square coloring (each cell gets a color from its list).

The book's proof uses the theory of list coloring for bipartite graphs,
specifically kernel-perfect orientations.
-/

namespace ProofsInTheBook.Chapter34

/-- Cells in an `n × n` Dinitz array. -/
abbrev Cell (n : ℕ) : Type := Fin n × Fin n

/-- A directed orientation relation supported on an undirected adjacency relation. -/
def OrientedEdge {V : Type*} (adj : V → V → Prop) (orient : V → V → Prop) : Prop :=
  ∀ ⦃u v⦄, orient u v → adj u v

/-- Out-neighbors of `v` inside a finite vertex set `S`. -/
def outNeighborsIn {V : Type*} [DecidableEq V] (S : Finset V)
    (orient : V → V → Prop) [DecidableRel orient] (v : V) : Finset V :=
  S.filter fun w => orient v w

/-- Two cells conflict when they are distinct and lie in a common row or column. -/
def LatinConflict {n : ℕ} (a b : Cell n) : Prop :=
  a ≠ b ∧ (a.1 = b.1 ∨ a.2 = b.2)

/-- The cyclic Latin square value used in Galvin's orientation. -/
noncomputable def cyclicLatinValue {n : ℕ} (cell : Cell n) : Fin n :=
  cell.1 + cell.2

/--
Galvin's orientation of the Dinitz conflict graph from the cyclic Latin square:
within a row edges point toward larger entries, while within a column they
point toward smaller entries.
-/
noncomputable def dinitzOrient {n : ℕ} (a b : Cell n) : Prop :=
  LatinConflict a b ∧
    ((a.1 = b.1 ∧ cyclicLatinValue a < cyclicLatinValue b) ∨
      (a.2 = b.2 ∧ cyclicLatinValue b < cyclicLatinValue a))

noncomputable instance dinitzOrient_decidableRel {n : ℕ} : DecidableRel (@dinitzOrient n) :=
  Classical.decRel _











/-- A proper Dinitz/Latin coloring: conflicting cells receive different colors. -/
def ProperArrayColoring {n : ℕ} {α : Type*} (color : Cell n → α) : Prop :=
  ∀ a b, LatinConflict a b → color a ≠ color b

/-- A coloring respects the list assignment when every cell receives a color from its list. -/
def RespectsLists {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  ∀ cell, color cell ∈ lists cell

/-- The target object in Dinitz's problem: list-respecting and Latin-proper. -/
def DinitzSolution {n : ℕ} {α : Type*} (lists : Cell n → Finset α)
    (color : Cell n → α) : Prop :=
  RespectsLists lists color ∧ ProperArrayColoring color











/-! ### Galvin's actual kernel-perfect list-coloring interface -/

/-- A kernel in an induced directed graph on `S`. -/
def IsKernelIn {V : Type*} [DecidableEq V] (S K : Finset V)
    (adj orient : V → V → Prop) : Prop :=
  K ⊆ S ∧
    (∀ u ∈ K, ∀ v ∈ K, adj u v → u = v) ∧
    ∀ u ∈ S, u ∉ K → ∃ v ∈ K, orient u v

/--
The kernel-perfect premise actually used by Galvin: every nonempty induced
subgraph has a kernel.
-/
def KernelPerfectOn {V : Type*} [DecidableEq V] (S : Finset V)
    (adj orient : V → V → Prop) : Prop :=
  ∀ T : Finset V, T ⊆ S → T.Nonempty → ∃ K : Finset V, IsKernelIn T K adj orient

/-- A list coloring of a finite induced graph. -/
def ListColoringOn {V α : Type*} [DecidableEq V] [DecidableEq α]
    (S : Finset V) (adj : V → V → Prop) (lists : V → Finset α)
    (color : V → α) : Prop :=
  (∀ v ∈ S, color v ∈ lists v) ∧
    ∀ u ∈ S, ∀ v ∈ S, adj u v → u ≠ v → color u ≠ color v





/-! ### Stable matchings give Galvin kernels for the Dinitz orientation -/

/-- A matching in an induced Dinitz conflict graph. -/
def MatchingCells {n : ℕ} (A M : Finset (Cell n)) : Prop :=
  M ⊆ A ∧
    ∀ u ∈ M, ∀ v ∈ M, LatinConflict u v → u = v

/-- A cell is dominated by a matching if it has an outgoing arc to a matched cell. -/
def DominatedByMatching {n : ℕ} (M : Finset (Cell n)) (cell : Cell n) : Prop :=
  ∃ matched ∈ M, dinitzOrient cell matched

/--
A stable matching for the Dinitz orientation: unmatched cells in `A` point to
some matched cell. This is the exact kernel condition supplied by Galvin's
stable-matching argument.
-/
def StableMatching {n : ℕ} (A M : Finset (Cell n)) : Prop :=
  MatchingCells A M ∧
    ∀ cell ∈ A, cell ∉ M → DominatedByMatching M cell

















end ProofsInTheBook.Chapter34


