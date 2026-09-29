-- Prove2me | solution 1 for RomanDomination.min_succ_le_weight_of_isURRDF_K
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:51:45.555604+00:00
-- url     : https://prove2.me/submissions/55254c56-10ad-48ca-8d81-01886829d37c

-- Sol generated from Geometry/RomanDomination/PerfectUnique.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_K_adj_inl_inr
import Theorems.Thm_RomanDomination_K_adj_inr_inl
import Theorems.Thm_RomanDomination_K_not_adj_inl_inl
import Theorems.Thm_RomanDomination_K_not_adj_inr_inr
import Theorems.Thm_RomanDomination_m_le_left_sum
import Theorems.Thm_RomanDomination_m_succ_le_left_sum
import Theorems.Thm_RomanDomination_n_le_right_sum
import Theorems.Thm_RomanDomination_n_succ_le_right_sum
import Theorems.Thm_RomanDomination_weight_sum_type
/-
# Perfect and unique response Roman domination of the complete bipartite graph

This file computes exactly the two "uniqueness flavoured" Roman-type domination
parameters of the complete bipartite graph `K_{m,n}` for all `m, n ≥ 1`:

```
γ_p(K_{m,n}) = min 4 (min (m+1) (n+1))     (perfect Roman domination)
u  (K_{m,n}) = min (m+1) (n+1)             (unique response Roman domination)
```

The perfect Roman value coincides with the ordinary Roman domination number
`γ_R(K_{m,n})`, computed in `Geometry.RomanDomination.ConvexBipartite`: the lower
bound is inherited from `γ_R ≤ γ_p`, and the three optimal Roman dominating
functions of `K_{m,n}` happen to be *perfect*.

The unique response value is genuinely different, and is *not* bounded by `4`: a
vertex labelled `2` in a complete bipartite graph forbids every vertex on the
opposite side from carrying a positive label, so one whole side must be labelled
`0` and the other side must avoid `0` entirely.  Consequently the gap
`u(K_{m,n}) - γ_p(K_{m,n}) = min m n - 3` is unbounded.
-/


open RomanDomination

open Finset

/-! ### Lower-bound helpers for `γ_p` and `u` -/


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]




/-! ### The three optimal labellings are perfect and (partly) unique response -/


variable {m n : ℕ}





/-! ### The perfect Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}




/-! ### The unique response Roman domination number of `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}

/-- In a unique response Roman dominating function of `K_{m,n}`, a left vertex
labelled `2` forces the entire right side to be labelled `0`. -/
lemma right_zero_of_left_two (hf : IsURRDF (K m n) f) {i₀ : Fin m}
    (h₀ : f (Sum.inl i₀) = 2) : ∀ j, f (Sum.inr j) = 0 := by
  intro j
  by_contra h
  exact hf.2.2 (Sum.inr j) (Nat.pos_of_ne_zero h) (Sum.inl i₀) (K_adj_inr_inl j i₀) h₀

/-- In a unique response Roman dominating function of `K_{m,n}`, a right vertex
labelled `2` forces the entire left side to be labelled `0`. -/
lemma left_zero_of_right_two (hf : IsURRDF (K m n) f) {j₀ : Fin n}
    (h₀ : f (Sum.inr j₀) = 2) : ∀ i, f (Sum.inl i) = 0 := by
  intro i
  by_contra h
  exact hf.2.2 (Sum.inl i) (Nat.pos_of_ne_zero h) (Sum.inr j₀) (K_adj_inl_inr i j₀) h₀

/-- If no right vertex is labelled `2`, no left vertex may be labelled `0`. -/
lemma left_ne_zero_of_no_right_two (hf : IsURRDF (K m n) f) (h : ∀ j, f (Sum.inr j) ≠ 2) :
    ∀ i, f (Sum.inl i) ≠ 0 := by
  intro i hi
  obtain ⟨u, ⟨hadj, hu⟩, -⟩ := hf.2.1 (Sum.inl i) hi
  match u with
  | Sum.inl i' => exact absurd hadj (K_not_adj_inl_inl i i')
  | Sum.inr j => exact h j hu

/-- If no left vertex is labelled `2`, no right vertex may be labelled `0`. -/
lemma right_ne_zero_of_no_left_two (hf : IsURRDF (K m n) f) (h : ∀ i, f (Sum.inl i) ≠ 2) :
    ∀ j, f (Sum.inr j) ≠ 0 := by
  intro j hj
  obtain ⟨u, ⟨hadj, hu⟩, -⟩ := hf.2.1 (Sum.inr j) hj
  match u with
  | Sum.inr j' => exact absurd hadj (K_not_adj_inr_inr j j')
  | Sum.inl i => exact h i hu






open RomanDomination in
theorem solution(hm : 1 ≤ m) (hf : IsURRDF (K m n) f) :
    min (m + 1) (n + 1) ≤ weight f := by
  rw [weight_sum_type]
  by_cases hA : ∃ i, f (Sum.inl i) = 2
  · obtain ⟨i₀, h₀⟩ := hA
    have hB0 := right_zero_of_left_two hf h₀
    have hAne : ∀ i, f (Sum.inl i) ≠ 0 :=
      left_ne_zero_of_no_right_two hf (fun j => by rw [hB0 j]; omega)
    have := m_succ_le_left_sum hAne h₀
    omega
  · push_neg at hA
    by_cases hB : ∃ j, f (Sum.inr j) = 2
    · obtain ⟨j₀, h₀⟩ := hB
      have hA0 := left_zero_of_right_two hf h₀
      have hBne : ∀ j, f (Sum.inr j) ≠ 0 :=
        right_ne_zero_of_no_left_two hf (fun i => by rw [hA0 i]; omega)
      have := n_succ_le_right_sum hBne h₀
      omega
    · push_neg at hB
      have h1 := m_le_left_sum (left_ne_zero_of_no_right_two hf hB)
      have h2 := n_le_right_sum (right_ne_zero_of_no_left_two hf hA)
      omega
