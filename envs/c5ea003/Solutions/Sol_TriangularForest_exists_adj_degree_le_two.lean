-- Prove2me | solution 1 for TriangularForest.exists_adj_degree_le_two
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:50:29.836544+00:00
-- url     : https://prove2.me/submissions/b854575f-30c0-4462-8474-19915808121c

-- Sol generated from Logic/TriangularForest/SharpBound.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_degree_le_two_of_maxPath_endpoint
import Theorems.Thm_TriangularForest_degree_second_le_two
import Theorems.Thm_TriangularForest_exists_maxPath
import Theorems.Thm_TriangularForest_maxPath_idx_injOn
import Theorems.Thm_TriangularForest_maxPath_neighbor_idx
import Theorems.Thm_TriangularForest_maxPath_neighbor_mem_support

/-!
# The sharp sparsity bound for triangular forests

A connected triangular forest on `n` vertices with `t` triangular blocks has `n - 1 + t` edges
and `2t ≤ n - 1`, so `2e ≤ 3(n-1)`.  Here we prove this sharp bound
(`TriangularForest.two_mul_card_edgeFinset_le`) without developing block decompositions, by
refining the longest-path argument of `Logic.TriangularForest.Sparsity`:

* `TriangularForest.degree_second_le_two` — if `p = a → v₁ → v₂ → ⋯` is a longest path in a
  triangular forest and `a` is also adjacent to `v₂` (which happens as soon as `a` has degree
  two), then the *second* vertex `v₁` also has degree at most two.  Neighbours of `v₁` off the
  path would allow the reroute `y → v₁ → a → v₂ → ⋯`, which is longer; neighbours further along
  the path close a cycle of length `≥ 4`, except for the vertex `v₃`, which is excluded by the
  4-cycle `a → v₁ → v₃ → v₂ → a`.
* `TriangularForest.exists_adj_degree_le_two` — hence a triangular forest of minimum degree at
  least two contains an *edge* both of whose endpoints have degree two (a leaf triangle).
* Deleting such a pair removes two vertices and exactly three edges, which powers the induction
  giving `2e ≤ 3(n-1)`.

As a consequence `Kₙ` fails to decompose into two triangular forests already for `n ≥ 6`, which
combined with `TriangularForest.completeGraph_decomposesIntoTwo_five` pins the threshold
exactly: `Kₙ` decomposes into two triangular forests if and only if `n ≤ 5`.
-/

open TriangularForest

open SimpleGraph Finset

variable {V : Type*} {G : SimpleGraph V}

/-- A walk of length at least two starts with two `cons`. -/
theorem exists_cons_cons_of_two_le_length {a b : V} (p : G.Walk a b) (h : 2 ≤ p.length) :
    ∃ (v₁ v₂ : V) (h₀₁ : G.Adj a v₁) (h₁₂ : G.Adj v₁ v₂) (r : G.Walk v₂ b),
      p = Walk.cons h₀₁ (Walk.cons h₁₂ r) := by
  cases p with
  | nil => simp at h
  | cons h₀₁ q =>
    cases q with
    | nil => simp at h
    | cons h₁₂ r => exact ⟨_, _, h₀₁, h₁₂, r, rfl⟩


variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]















open TriangularForest in
theorem solution[Nonempty V] (hG : IsTriangularForest G)
    (hmin : ∀ v : V, 2 ≤ G.degree v) :
    ∃ u v : V, G.Adj u v ∧ G.degree u ≤ 2 ∧ G.degree v ≤ 2 := by
  classical
  obtain ⟨a, b, p, hp, hmax⟩ := exists_maxPath G
  have hdega : G.degree a ≤ 2 := degree_le_two_of_maxPath_endpoint hG p hp hmax
  have hdega' : G.degree a = 2 := le_antisymm hdega (hmin a)
  -- position `2` along `p` is occupied by a neighbour of `a`
  have himg : (G.neighborFinset a).image (fun x => p.support.idxOf x) = {1, 2} := by
    refine Finset.eq_of_subset_of_card_le ?_ ?_
    · intro i hi
      simp only [Finset.mem_image] at hi
      obtain ⟨x, hx, rfl⟩ := hi
      have := maxPath_neighbor_idx hG p hp hmax hx
      simpa using this
    · rw [Finset.card_image_of_injOn (maxPath_idx_injOn p hp hmax)]
      simp [card_neighborFinset_eq_degree, hdega']
  have h2img : (2 : ℕ) ∈ (G.neighborFinset a).image (fun x => p.support.idxOf x) := by
    rw [himg]; simp
  simp only [Finset.mem_image] at h2img
  obtain ⟨x, hx, hx2⟩ := h2img
  have hxs : x ∈ p.support := maxPath_neighbor_mem_support p hp hmax hx
  have hxgv : p.getVert 2 = x := by
    have := p.getVert_support_idxOf hxs
    rwa [hx2] at this
  have hlen : 2 ≤ p.length := by
    by_contra hcon
    push_neg at hcon
    have hidx : p.support.idxOf x < p.support.length := List.idxOf_lt_length_of_mem hxs
    rw [Walk.length_support] at hidx
    omega
  obtain ⟨v₁, v₂, h₀₁, h₁₂, r, rfl⟩ := exists_cons_cons_of_two_le_length p hlen
  have ha₂ : G.Adj a v₂ := by
    have : v₂ = x := by simpa using hxgv
    rw [this]
    exact (G.mem_neighborFinset a x).1 hx
  refine ⟨a, v₁, h₀₁, hdega, degree_second_le_two hG h₀₁ h₁₂ r hp hmax ha₂⟩
