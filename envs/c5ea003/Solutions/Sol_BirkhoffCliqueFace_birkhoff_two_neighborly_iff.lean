-- Prove2me | solution 1 for BirkhoffCliqueFace.birkhoff_two_neighborly_iff
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:49:48.524251+00:00
-- url     : https://prove2.me/submissions/f9a8cb4a-997e-49a2-9b30-5cc063538795

-- Sol generated from Geometry/RamseyTheory/BirkhoffCliqueFace.lean
import Mathlib
import Definitions.Def_Geometry_RamseyTheory_BirkhoffCliqueFace
import Theorems.Thm_BirkhoffCliqueFace_exists_bad_face

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










/-- For `n ≤ 3` every non-identity permutation of `Fin n` is a single cycle. -/
lemma isCycle_of_ne_one (hn : n ≤ 3) (ρ : Perm (Fin n)) (h : ρ ≠ 1) : ρ.IsCycle := by
  rw [← Equiv.Perm.card_cycleType_eq_one]
  revert h ρ
  interval_cases n <;> decide


/-- If `n ≤ 3`, the graph `G_n` is complete: any two distinct permutations are adjacent. -/
lemma adj_of_ne (hn : n ≤ 3) (σ τ : Perm (Fin n)) (h : σ ≠ τ) :
    (BirkhoffGraph n).Adj σ τ := by
  refine ⟨h, ?_⟩
  apply isCycle_of_ne_one n hn
  intro hcontra
  apply h
  have h2 : σ⁻¹ = τ⁻¹ := mul_eq_one_iff_eq_inv.mp hcontra
  exact inv_inj.mp h2





open BirkhoffCliqueFace in
theorem solution:
    (∀ σ τ : Perm (Fin n), σ ≠ τ → (BirkhoffGraph n).Adj σ τ) ↔ n ≤ 3 := by
  constructor
  · intro h
    by_contra hlt
    push_neg at hlt
    -- reuse the bad face: it produces two distinct non-adjacent vertices
    obtain ⟨F, _, hnot⟩ := exists_bad_face n hlt
    apply hnot
    intro x _ y _ hxy
    exact h x y hxy
  · intro hn σ τ hne
    exact adj_of_ne n hn σ τ hne
