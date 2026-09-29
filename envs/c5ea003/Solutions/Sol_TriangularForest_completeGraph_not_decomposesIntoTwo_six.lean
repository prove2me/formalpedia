-- Prove2me | solution 1 for TriangularForest.completeGraph_not_decomposesIntoTwo_six
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-13T18:44:59.722918+00:00
-- url     : https://prove2.me/submissions/3d773b5d-6075-492d-8528-22b50134b9ca

-- Sol generated from Logic/TriangularForest/SharpBound.lean
import Mathlib
import Definitions.Def_Logic_TriangularForest_Decomposition
import Definitions.Def_Logic_TriangularForest_Defs
import Theorems.Thm_TriangularForest_card_edgeFinset_le_of_le_sup
import Theorems.Thm_TriangularForest_two_mul_card_edgeFinset_le

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










/-- A graph on `n ≥ 1` vertices decomposing into two triangular forests has at most
`2⌊3(n-1)/2⌋` edges. -/
theorem card_edgeFinset_le_of_decomposesIntoTwo' {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : DecomposesIntoTwo G)
    (hcard : 1 ≤ Fintype.card V) :
    ∃ e₁ e₂ : ℕ, #G.edgeFinset ≤ e₁ + e₂ ∧ 2 * e₁ ≤ 3 * (Fintype.card V - 1) ∧
      2 * e₂ ≤ 3 * (Fintype.card V - 1) := by
  classical
  obtain ⟨G₁, G₂, h₁, h₂, -, hsup⟩ := hG
  refine ⟨#G₁.edgeFinset, #G₂.edgeFinset, ?_, two_mul_card_edgeFinset_le G₁ h₁ hcard,
    two_mul_card_edgeFinset_le G₂ h₂ hcard⟩
  exact card_edgeFinset_le_of_le_sup (le_of_eq hsup.symm)





open TriangularForest in
theorem solution{n : ℕ} (hn : 6 ≤ n) :
    ¬ DecomposesIntoTwo (⊤ : SimpleGraph (Fin n)) := by
  intro hdec
  have hcard : 1 ≤ Fintype.card (Fin n) := by simp; omega
  obtain ⟨e₁, e₂, hle, hb₁, hb₂⟩ :=
    card_edgeFinset_le_of_decomposesIntoTwo' (⊤ : SimpleGraph (Fin n)) hdec hcard
  have htop : #(⊤ : SimpleGraph (Fin n)).edgeFinset = n.choose 2 := by
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two]
    simp
  have hle' : n.choose 2 ≤ e₁ + e₂ := le_trans (le_of_eq htop.symm) hle
  rw [Fintype.card_fin] at hb₁ hb₂
  clear hle htop
  have hchoose : 2 * n.choose 2 = n * (n - 1) := by
    obtain ⟨r, hr⟩ := Nat.even_mul_pred_self n
    rw [Nat.choose_two_right, hr]
    omega
  rcases eq_or_lt_of_le hn with h6 | h7
  · subst_vars
    rw [show Nat.choose 6 2 = 15 by decide] at hle'
    omega
  · -- for `n ≥ 7` the count `n(n-1)` already beats `6(n-1)`
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [Nat.add_sub_cancel] at hchoose hb₁ hb₂ h7
    nlinarith [hle', hchoose, hb₁, hb₂, h7]
