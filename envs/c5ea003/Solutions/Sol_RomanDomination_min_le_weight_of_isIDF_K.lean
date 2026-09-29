-- Prove2me | solution 1 for RomanDomination.min_le_weight_of_isIDF_K
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:43.670574+00:00
-- url     : https://prove2.me/submissions/55caaeb8-d6cc-4bb1-88c5-de1d889b8c3a

-- Sol generated from Geometry/RomanDomination/ConvexBipartite.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_four_le_weight_of_isIDF_zero_both
import Theorems.Thm_RomanDomination_m_le_left_sum
import Theorems.Thm_RomanDomination_n_le_right_sum
import Theorems.Thm_RomanDomination_weight_sum_type
/-
# Convex bipartite graphs and exact Roman-type domination numbers of `K_{m,n}`

A bipartite graph with parts `A` and `B` is **convex** (with respect to a linear
order on `A`) when the neighbourhood of every vertex of `B` is an order-convex
subset of `A`, i.e. an interval.  This interval structure is exactly what makes the
left-to-right dynamic programming algorithms for Roman-type domination possible on
this graph class.

Here we

* define `IsConvexBipartite` for graphs on `Fin m ⊕ Fin n`,
* show that a convex bipartite graph is `2`-colourable,
* show that the complete bipartite graph `K_{m,n}` is convex bipartite, and
* compute *exactly* the Roman domination number and the Italian (Roman-`{2}`)
  domination number of `K_{m,n}`:

```
γ_R(K_{m,n}) = min 4 (min (m+1) (n+1))     (m, n ≥ 1)
γ_I(K_{m,n}) = min 4 (min m n)             (m, n ≥ 2)
```
-/


open RomanDomination

open Finset

/-! ### Convex bipartite graphs -/




variable (m n : ℕ)



variable {m n}





variable (m n)



/-! ### Splitting weights over the two sides -/


variable {m n : ℕ}


/-- The neighbourhood sum of a left vertex of `K_{m,n}` is the right side weight. -/
lemma K_neighbor_sum_inl (f : Fin m ⊕ Fin n → ℕ) (i : Fin m) :
    ∑ u ∈ (K m n).neighborFinset (Sum.inl i), f u = ∑ j, f (Sum.inr j) := by
  have h : (K m n).neighborFinset (Sum.inl i) = Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩ := by
    ext u
    simp [K, completeBipartiteGraph_adj]
    rcases u with ⟨⟩ <;> simp
  rw [h, Finset.sum_map]
  simp

/-- The neighbourhood sum of a right vertex of `K_{m,n}` is the left side weight. -/
lemma K_neighbor_sum_inr (f : Fin m ⊕ Fin n → ℕ) (j : Fin n) :
    ∑ u ∈ (K m n).neighborFinset (Sum.inr j), f u = ∑ i, f (Sum.inl i) := by
  have h : (K m n).neighborFinset (Sum.inr j) = Finset.univ.map ⟨Sum.inl, Sum.inl_injective⟩ := by
    ext u
    simp [K, completeBipartiteGraph_adj]
    rcases u with ⟨⟩ <;> simp
  rw [h, Finset.sum_map]
  simp





/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}














variable {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Italian domination number of `K_{m,n}` -/


variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}


/-- If no left vertex is labelled `0`, the total weight is at least `m`. -/
lemma m_le_weight_of_no_zero_left (h : ∀ i, f (Sum.inl i) ≠ 0) : m ≤ weight f := by
  rw [weight_sum_type]
  have := m_le_left_sum h
  omega






open RomanDomination in
theorem solution(hf : IsIDF (K m n) f) : min 4 (min m n) ≤ weight f := by
  by_cases hA : ∃ i, f (Sum.inl i) = 0
  case pos =>
    by_cases hB : ∃ j, f (Sum.inr j) = 0
    case pos =>
      exact le_trans (min_le_left _ _) (four_le_weight_of_isIDF_zero_both hf hA hB)
    case neg =>
      push_neg at hB
      rw [weight_sum_type]
      have hright : 2 ≤ ∑ j, f (Sum.inr j) := by
        obtain ⟨i₀, hi₀⟩ := hA
        have := hf.2 (Sum.inl i₀) hi₀
        rw [K_neighbor_sum_inl] at this
        exact this
      have hright' : n ≤ ∑ j, f (Sum.inr j) := n_le_right_sum hB
      omega
  case neg =>
    by_cases hB : ∃ j, f (Sum.inr j) = 0
    case pos =>
      push_neg at hA
      rw [weight_sum_type]
      have hleft : 2 ≤ ∑ i, f (Sum.inl i) := by
        obtain ⟨j₀, hj₀⟩ := hB
        have := hf.2 (Sum.inr j₀) hj₀
        rw [K_neighbor_sum_inr] at this
        exact this
      have hleft' : m ≤ ∑ i, f (Sum.inl i) := m_le_left_sum hA
      omega
    case neg =>
      push_neg at hA hB
      have h1 := m_le_weight_of_no_zero_left hA
      omega
