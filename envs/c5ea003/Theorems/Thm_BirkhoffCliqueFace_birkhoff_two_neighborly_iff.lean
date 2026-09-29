-- Prove2me | Theorems.Thm_BirkhoffCliqueFace_birkhoff_two_neighborly_iff
-- name    : BirkhoffCliqueFace.birkhoff_two_neighborly_iff
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:04:56.709716+00:00
-- url     : https://prove2.me/theorems/1aedf72a-dddd-4c64-8d60-40c292e4cae4
-- title:
--   Equivalent formulation.
-- statement:
--   **Equivalent formulation.** `B_n` is 2-neighborly (every two distinct vertices form
--   an edge of the 1-skeleton) if and only if `n ≤ 3`.
--
--   ```lean
--   theorem BirkhoffCliqueFace.birkhoff_two_neighborly_iff:
--       (∀ σ τ : Perm (Fin n), σ ≠ τ → (BirkhoffGraph n).Adj σ τ) ↔ n ≤ 3 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RamseyTheory/BirkhoffCliqueFace.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RamseyTheory/BirkhoffCliqueFace.lean#L249

-- Thm stub generated from Geometry/RamseyTheory/BirkhoffCliqueFace.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_BirkhoffCliqueFace

/-!
# The clique–face property of the Birkhoff polytope

The Birkhoff polytope `B_n` is the convex hull of the `n × n` permutation matrices
(equivalently, the polytope of doubly stochastic matrices).  Its vertices are exactly
the permutation matrices, and its **1-skeleton** `G_n` is the graph on `S_n` in which two
permutations are adjacent iff their permutation matrices form an edge of `B_n`.  By the
classical adjacency criterion for the assignment/Birkhoff polytope (Brualdi–Gibson),
`σ` and `τ` are adjacent iff `σ⁻¹ * τ` is a single cycle; we take this combinatorial
description as the definition of the graph `BirkhoffGraph n`.

## What is proved here

We prove that **every face of `B_n` has a vertex set which is a clique of `G_n`
iff `n ≤ 3`** (`birkhoff_cliqueface_iff`).  Equivalently, `B_n` is *2-neighborly*
(every two distinct vertices form an edge) iff `n ≤ 3` (`birkhoff_two_neighborly_iff`).

* For `n ≤ 3` every non-identity element of `S_n` is a single cycle, so `G_n` is a
  complete graph; hence *every* set of vertices — in particular every face's vertex
  set — is a clique.
* For `n ≥ 4` the four permutations `1, (a b), (c d), (a b)(c d)` (with `a,b,c,d`
  distinct) all have support inside the `2 × 2` block pattern `Z`, and the face
  cut out by the supporting functional `∑_{(i,j) ∈ Z} x i j ≤ n` contains both the
  identity and `(a b)(c d) = swap a b * swap c d`.  Since `(a b)(c d)` is a product of
  two disjoint transpositions, it is **not** a single cycle, so `1` and `(a b)(c d)`
  are non-adjacent in `G_n`; thus this face's vertex set is not a clique.

## Note on the problem statement

The originally requested phrasing ("every clique is the vertex set of some face,
iff `n ≤ 3`", with adjacency described as "differ by a transposition") is internally
inconsistent: the *transposition* Cayley graph is bipartite (triangle-free), so its
cliques always have ≤ 2 vertices and are always faces, for every `n`; and with the genuine
1-skeleton the *literal* "every clique is a face" direction already fails at `n = 3`
(e.g. the clique `{1,(1 2),(1 2 3),(1 3 2)}` of `B_3` is not a face).  The threshold
`n ≤ 3` is exactly the 2-neighborliness threshold, i.e. the direction formalized here:
*every face's vertex set is a clique*.  The permutations `1,(1 2),(3 4),(1 2)(3 4)`
mentioned in the prompt occur here in their correct role, as the vertices of a face of
`B_4` whose vertex set fails to be a clique.
-/

open Equiv Equiv.Perm Finset

open BirkhoffCliqueFace

variable (n : ℕ)

theorem BirkhoffCliqueFace.birkhoff_two_neighborly_iff:
    (∀ σ τ : Perm (Fin n), σ ≠ τ → (BirkhoffGraph n).Adj σ τ) ↔ n ≤ 3 := by sorry
