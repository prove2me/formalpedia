-- Prove2me | Definitions.Def_Geometry_RamseyTheory_BirkhoffCliqueFace
-- name    : Geometry_RamseyTheory_BirkhoffCliqueFace
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T00:52:01.806662+00:00
-- url     : https://prove2.me/theorems/646e8999-a374-4174-9055-60948a26798b
-- title:
--   Aether Catalog definitions — Geometry_RamseyTheory_BirkhoffCliqueFace
-- statement:
--   Definition bundle for the Aether Catalog module `Geometry.RamseyTheory.BirkhoffCliqueFace`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Geometry/RamseyTheory/BirkhoffCliqueFace.lean by skeleton subtraction
import Mathlib

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

namespace BirkhoffCliqueFace

variable (n : ℕ)

/-- The permutation matrix of `σ`: a `1` in position `(i, σ i)`, `0` elsewhere. -/
noncomputable def permMat (σ : Perm (Fin n)) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => if σ i = j then (1 : ℝ) else 0

/-- The **Birkhoff polytope** `B_n`: the convex hull of the permutation matrices. -/
def Birkhoff : Set (Matrix (Fin n) (Fin n) ℝ) :=
  convexHull ℝ (Set.range (permMat n))

/-- A **face** of `B_n`: the intersection of `B_n` with a supporting hyperplane,
i.e. the set where a linear functional `f` attains its maximum value `c` over `B_n`. -/
def IsFace (F : Set (Matrix (Fin n) (Fin n) ℝ)) : Prop :=
  ∃ (f : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ x ∈ Birkhoff n, f x ≤ c) ∧ F = {x | x ∈ Birkhoff n ∧ f x = c}

/-- The **vertex set** of a face: those permutations whose matrix lies in the face. -/
def faceVertices (F : Set (Matrix (Fin n) (Fin n) ℝ)) : Set (Perm (Fin n)) :=
  {σ | permMat n σ ∈ F}

/-- The **1-skeleton graph** `G_n` of `B_n`: two distinct permutations are adjacent iff
`σ⁻¹ * τ` is a single cycle (the classical Birkhoff-polytope edge criterion). -/
def BirkhoffGraph : SimpleGraph (Perm (Fin n)) where
  Adj σ τ := σ ≠ τ ∧ (σ⁻¹ * τ).IsCycle
  symm := by
    rintro σ τ ⟨hne, hcyc⟩
    refine ⟨hne.symm, ?_⟩
    have h : (σ⁻¹ * τ)⁻¹ = τ⁻¹ * σ := by group
    rw [← h]; exact hcyc.inv
  loopless := ⟨fun σ h => h.1 rfl⟩

/-- The **clique–face property**: the vertex set of every face is a clique of `G_n`
(equivalently, `B_n` is 2-neighborly). -/
def CliqueFaceProperty : Prop :=
  ∀ F, IsFace n F → (BirkhoffGraph n).IsClique (faceVertices n F)

/-- The linear functional `x ↦ ∑_{i,j} W i j * x i j` associated to a cost matrix `W`. -/
noncomputable def costLin (W : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] ℝ :=
  ∑ i, ∑ j, (W i j) • Matrix.entryLinearMap ℝ ℝ i j









end BirkhoffCliqueFace


