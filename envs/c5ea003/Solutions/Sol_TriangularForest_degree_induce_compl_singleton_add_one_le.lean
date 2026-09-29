-- Prove2me | solution 1 for TriangularForest.degree_induce_compl_singleton_add_one_le
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:45:00.241381+00:00
-- url     : https://prove2.me/submissions/6dc3dfc2-cb4d-4227-b1b7-a1214f86954e

-- Sol generated from Logic/TriangularForest/SharpBound.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition

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



variable [Fintype V] [DecidableEq V] [DecidableRel G.Adj]















open TriangularForest in
theorem solution[Fintype V] [DecidableEq V]
    [DecidableRel G.Adj] {u v : V} (h : G.Adj v u) (hv : v ∈ ({u}ᶜ : Set V)) :
    (G.induce ({u}ᶜ : Set V)).degree ⟨v, hv⟩ + 1 ≤ G.degree v := by
  classical
  have hmaps : Set.MapsTo (fun w : ({u}ᶜ : Set V) => (w : V))
      (((G.induce ({u}ᶜ : Set V)).neighborFinset ⟨v, hv⟩ : Finset _) : Set _)
      (((G.neighborFinset v).erase u : Finset V) : Set V) := by
    intro w hw
    simp only [Finset.mem_coe, mem_neighborFinset] at hw
    simp only [Finset.mem_coe, Finset.mem_erase, mem_neighborFinset]
    refine ⟨fun hh => ?_, hw⟩
    exact (w.2 : (w : V) ∈ ({u}ᶜ : Set V)) (by simp [hh])
  have hcard := Finset.card_le_card_of_injOn _ hmaps (Subtype.val_injective.injOn)
  rw [Finset.card_erase_of_mem (by simpa using h)] at hcard
  have hpos : 1 ≤ G.degree v := by
    rw [← card_neighborFinset_eq_degree]
    exact Finset.card_pos.2 ⟨u, by simpa using h⟩
  rw [card_neighborFinset_eq_degree, card_neighborFinset_eq_degree] at hcard
  omega
