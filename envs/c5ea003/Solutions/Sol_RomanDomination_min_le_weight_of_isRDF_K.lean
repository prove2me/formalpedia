-- Prove2me | solution 1 for RomanDomination.min_le_weight_of_isRDF_K
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:48:08.084259+00:00
-- url     : https://prove2.me/submissions/bbb4a5cb-a915-4af9-a676-a6ac65763265

-- Sol generated from Geometry/RomanDomination/ConvexBipartite.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_K_not_adj_inl_inl
import Theorems.Thm_RomanDomination_K_not_adj_inr_inr
import Theorems.Thm_RomanDomination_m_le_left_sum
import Theorems.Thm_RomanDomination_m_succ_le_left_sum
import Theorems.Thm_RomanDomination_n_le_right_sum
import Theorems.Thm_RomanDomination_n_succ_le_right_sum
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






/-- A single value bounds the sum from below. -/
lemma le_sum_of_le {α : Type*} [Fintype α] {g : α → ℕ} {a₀ : α} {c : ℕ} (h : c ≤ g a₀) :
    c ≤ ∑ a, g a := by
  exact le_trans h (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a₀))


/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}

/-- A left vertex labelled `0` forces a right vertex labelled `2`. -/
lemma exists_right_two (hf : IsRDF (K m n) f) {i : Fin m} (h0 : f (Sum.inl i) = 0) :
    ∃ j, f (Sum.inr j) = 2 := by
  obtain ⟨u, hadj, hu⟩ := hf.2 (Sum.inl i) h0
  match u with
  | Sum.inl j => exact absurd hadj (K_not_adj_inl_inl i j)
  | Sum.inr j => exact ⟨j, hu⟩

/-- A right vertex labelled `0` forces a left vertex labelled `2`. -/
lemma exists_left_two (hf : IsRDF (K m n) f) {j : Fin n} (h0 : f (Sum.inr j) = 0) :
    ∃ i, f (Sum.inl i) = 2 := by
  obtain ⟨u, hadj, hu⟩ := hf.2 (Sum.inr j) h0
  match u with
  | Sum.inr i => exact absurd hadj (K_not_adj_inr_inr j i)
  | Sum.inl i => exact ⟨i, hu⟩






/-! ### The Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}














variable {f : Fin m ⊕ Fin n → ℕ}

/-- Case both sides contain a `0`-vertex: the weight is at least `4`. -/
lemma four_le_weight_of_zero_both (hf : IsRDF (K m n) f)
    (hA : ∃ i, f (Sum.inl i) = 0) (hB : ∃ j, f (Sum.inr j) = 0) : 4 ≤ weight f := by
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ := hB
  obtain ⟨j', hj'⟩ := exists_right_two hf hi
  obtain ⟨i', hi'⟩ := exists_left_two hf hj
  rw [weight_sum_type]
  have hleft : 2 ≤ ∑ i, f (Sum.inl i) := le_sum_of_le hi'.ge
  have hright : 2 ≤ ∑ j, f (Sum.inr j) := le_sum_of_le hj'.ge
  omega

/-- Case a `0` on the left but none on the right: the weight is at least `n + 1`. -/
lemma succ_n_le_weight_of_zero_left (hf : IsRDF (K m n) f)
    (hA : ∃ i, f (Sum.inl i) = 0) (hB : ∀ j, f (Sum.inr j) ≠ 0) : n + 1 ≤ weight f := by
  obtain ⟨i, hi⟩ := hA
  obtain ⟨j, hj⟩ := exists_right_two hf hi
  rw [weight_sum_type]
  exact le_trans (n_succ_le_right_sum hB hj) (le_add_of_nonneg_left (Finset.sum_nonneg (fun _ _ => Nat.zero_le _)))

/-- Case a `0` on the right but none on the left: the weight is at least `m + 1`. -/
lemma succ_m_le_weight_of_zero_right (hf : IsRDF (K m n) f)
    (hA : ∀ i, f (Sum.inl i) ≠ 0) (hB : ∃ j, f (Sum.inr j) = 0) : m + 1 ≤ weight f := by
  obtain ⟨j, hj⟩ := hB
  obtain ⟨i₀, hi₀⟩ := exists_left_two hf hj
  rw [weight_sum_type]
  have := m_succ_le_left_sum hA hi₀
  exact le_trans this (le_add_of_nonneg_right (Nat.zero_le _))

/-- Case no `0` at all: the weight is at least `m + n`. -/
lemma add_le_weight_of_no_zero (hA : ∀ i, f (Sum.inl i) ≠ 0) (hB : ∀ j, f (Sum.inr j) ≠ 0) :
    m + n ≤ weight f := by
  rw [weight_sum_type]
  exact add_le_add (m_le_left_sum hA) (n_le_right_sum hB)




/-! ### The Italian domination number of `K_{m,n}` -/


variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}








open RomanDomination in
theorem solution(hm : 1 ≤ m) (hn : 1 ≤ n) (hf : IsRDF (K m n) f) :
    min 4 (min (m + 1) (n + 1)) ≤ weight f := by
  by_cases hA : ∃ i, f (Sum.inl i) = 0
  case pos =>
    by_cases hB : ∃ j, f (Sum.inr j) = 0
    case pos =>
      exact le_trans (min_le_left _ _) (four_le_weight_of_zero_both hf hA hB)
    case neg =>
      push_neg at hB
      have := succ_n_le_weight_of_zero_left hf hA hB
      omega
  case neg =>
    by_cases hB : ∃ j, f (Sum.inr j) = 0
    case pos =>
      push_neg at hA
      have := succ_m_le_weight_of_zero_right hf hA hB
      omega
    case neg =>
      push_neg at hA hB
      have := add_le_weight_of_no_zero hA hB
      omega
