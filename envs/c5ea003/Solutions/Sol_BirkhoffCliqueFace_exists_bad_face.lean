-- Prove2me | solution 1 for BirkhoffCliqueFace.exists_bad_face
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T02:48:01.061841+00:00
-- url     : https://prove2.me/submissions/546cf2db-e267-46d9-89ac-f277b07ae7d8

-- Sol generated from Geometry/RamseyTheory/BirkhoffCliqueFace.lean
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








lemma costLin_apply (W x : Matrix (Fin n) (Fin n) ℝ) :
    costLin n W x = ∑ i, ∑ j, W i j * x i j := by
  simp only [costLin, LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply,
    Matrix.entryLinearMap_apply, smul_eq_mul]

lemma costLin_permMat (W : Matrix (Fin n) (Fin n) ℝ) (σ : Perm (Fin n)) :
    costLin n W (permMat n σ) = ∑ i, W i (σ i) := by
  rw [costLin_apply]
  apply Finset.sum_congr rfl
  intro i _
  simp only [permMat, Matrix.of_apply, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq Finset.univ (σ i) (fun j => W i j)]
  simp


/-- A product of two disjoint transpositions is not a single cycle. -/
lemma not_isCycle_swap_mul_swap {α : Type*} [DecidableEq α] [Fintype α] {a b c d : α}
    (hab : a ≠ b) (hcd : c ≠ d) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) :
    ¬ ((swap a b) * (swap c d)).IsCycle := by
  have hdisj : (swap a b).Disjoint (swap c d) := by
    rw [Equiv.Perm.disjoint_iff_disjoint_support, support_swap hab, support_swap hcd]
    simp only [Finset.disjoint_left, Finset.mem_insert, Finset.mem_singleton]
    rintro x (rfl | rfl) <;> push_neg <;> constructor <;>
      intro hh <;> subst hh <;> simp_all
  rw [← card_cycleType_eq_one, hdisj.cycleType_mul,
      (isCycle_swap hab).cycleType, (isCycle_swap hcd).cycleType,
      support_swap hab, support_swap hcd, Finset.card_pair hab, Finset.card_pair hcd]
  decide






open BirkhoffCliqueFace in
theorem solution(hn : 4 ≤ n) :
    ∃ F, IsFace n F ∧ ¬ (BirkhoffGraph n).IsClique (faceVertices n F) := by
  -- four distinct indices
  set a : Fin n := ⟨0, by omega⟩ with ha
  set b : Fin n := ⟨1, by omega⟩ with hb
  set c : Fin n := ⟨2, by omega⟩ with hc
  set d : Fin n := ⟨3, by omega⟩ with hd
  have hab : a ≠ b := by simp [ha, hb]
  have hcd : c ≠ d := by simp [hc, hd]
  have hac : a ≠ c := by simp [ha, hc]
  have had : a ≠ d := by simp [ha, hd]
  have hbc : b ≠ c := by simp [hb, hc]
  have hbd : b ≠ d := by simp [hb, hd]
  -- the cost matrix supported on the 2×2 block pattern (and the diagonal)
  set W : Matrix (Fin n) (Fin n) ℝ := Matrix.of fun i j =>
    if i = j ∨ (i = a ∧ j = b) ∨ (i = b ∧ j = a) ∨ (i = c ∧ j = d) ∨ (i = d ∧ j = c)
      then 1 else 0 with hW
  -- the doubled transposition
  set τ : Perm (Fin n) := swap a b * swap c d with hτ
  -- values of τ
  have tab : τ a = b := by
    simp only [hτ, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hac had, Equiv.swap_apply_left]
  have tba : τ b = a := by
    simp only [hτ, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hbc hbd, Equiv.swap_apply_right]
  have tcd : τ c = d := by
    simp only [hτ, Perm.mul_apply, Equiv.swap_apply_left]
    exact Equiv.swap_apply_of_ne_of_ne had.symm hbd.symm
  have tdc : τ d = c := by
    simp only [hτ, Perm.mul_apply, Equiv.swap_apply_right]
    exact Equiv.swap_apply_of_ne_of_ne hac.symm hbc.symm
  -- W is bounded by 1 entrywise
  have hWle : ∀ i j, W i j ≤ (1 : ℝ) := by
    intro i j; simp only [hW, Matrix.of_apply]; split <;> norm_num
  -- value on the identity
  have hsum1 : (∑ i, W i ((1 : Perm (Fin n)) i)) = (n : ℝ) := by
    have h1 : ∀ i : Fin n, W i ((1 : Perm (Fin n)) i) = 1 := by
      intro i; simp only [hW, Matrix.of_apply, Perm.one_apply]; simp
    rw [Finset.sum_congr rfl (fun i _ => h1 i)]; simp
  -- value on τ
  have hsumτ : (∑ i, W i (τ i)) = (n : ℝ) := by
    have h2 : ∀ i : Fin n, W i (τ i) = 1 := by
      intro i
      have key : i = τ i ∨ (i = a ∧ τ i = b) ∨ (i = b ∧ τ i = a) ∨
          (i = c ∧ τ i = d) ∨ (i = d ∧ τ i = c) := by
        rcases eq_or_ne i a with rfl | hia
        · exact Or.inr (Or.inl ⟨rfl, tab⟩)
        rcases eq_or_ne i b with rfl | hib
        · exact Or.inr (Or.inr (Or.inl ⟨rfl, tba⟩))
        rcases eq_or_ne i c with rfl | hic
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, tcd⟩)))
        rcases eq_or_ne i d with rfl | hid
        · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, tdc⟩)))
        · exact Or.inl (by
            simp only [hτ, Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne hic hid,
              Equiv.swap_apply_of_ne_of_ne hia hib])
      simp only [hW, Matrix.of_apply]; rw [if_pos key]
    rw [Finset.sum_congr rfl (fun i _ => h2 i)]; simp
  -- the functional is bounded by n on every permutation, hence on B_n
  have permBound : ∀ σ : Perm (Fin n), (∑ i, W i (σ i)) ≤ (n : ℝ) := by
    intro σ
    calc (∑ i, W i (σ i)) ≤ ∑ _i : Fin n, (1 : ℝ) := by
            apply Finset.sum_le_sum; intro i _; exact hWle i (σ i)
      _ = (n : ℝ) := by simp
  have bound : ∀ x ∈ Birkhoff n, costLin n W x ≤ (n : ℝ) := by
    have hsub : Set.range (permMat n) ⊆ {y | costLin n W y ≤ (n : ℝ)} := by
      rintro _ ⟨σ, rfl⟩
      show costLin n W (permMat n σ) ≤ (n : ℝ)
      rw [costLin_permMat]; exact permBound σ
    have hconv : Convex ℝ {y | costLin n W y ≤ (n : ℝ)} :=
      (convex_Iic (n : ℝ)).is_linear_preimage (costLin n W).isLinear
    intro x hx
    exact convexHull_min hsub hconv hx
  -- the face
  set F : Set (Matrix (Fin n) (Fin n) ℝ) :=
    {x | x ∈ Birkhoff n ∧ costLin n W x = (n : ℝ)} with hF
  refine ⟨F, ⟨costLin n W, (n : ℝ), bound, hF⟩, ?_⟩
  -- membership facts
  have hmem1 : permMat n (1 : Perm (Fin n)) ∈ Birkhoff n :=
    subset_convexHull ℝ _ ⟨1, rfl⟩
  have hmemτ : permMat n τ ∈ Birkhoff n :=
    subset_convexHull ℝ _ ⟨τ, rfl⟩
  have hv1 : (1 : Perm (Fin n)) ∈ faceVertices n F := by
    refine ⟨hmem1, ?_⟩
    rw [costLin_permMat]; exact hsum1
  have hvτ : τ ∈ faceVertices n F := by
    refine ⟨hmemτ, ?_⟩
    rw [costLin_permMat]; exact hsumτ
  -- `1` and `τ` are distinct
  have hne : (1 : Perm (Fin n)) ≠ τ := by
    intro h
    have : a = τ a := by rw [← h]; rfl
    rw [tab] at this; exact hab this
  -- `τ` is not a single cycle, so `1` and `τ` are non-adjacent
  have hnotcyc : ¬ τ.IsCycle := not_isCycle_swap_mul_swap hab hcd hac had hbc hbd
  have hnotadj : ¬ (BirkhoffGraph n).Adj 1 τ := by
    rintro ⟨-, hcyc⟩
    apply hnotcyc
    simpa using hcyc
  -- conclude the vertex set is not a clique
  intro hclique
  exact hnotadj (hclique hv1 hvτ hne)
