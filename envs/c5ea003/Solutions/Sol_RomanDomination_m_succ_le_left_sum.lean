-- Prove2me | solution 1 for RomanDomination.m_succ_le_left_sum
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:45:28.172678+00:00
-- url     : https://prove2.me/submissions/f1485c41-1b7b-4ea3-82fd-79f30a6c318a

-- Sol generated from Geometry/RomanDomination/ConvexBipartite.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
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





/-- If every value is at least one and some value is at least `2`, the sum is at least
`card + 1`. -/
lemma card_succ_le_sum_of_one_le_of_two {α : Type*} [Fintype α] [DecidableEq α] {g : α → ℕ}
    (h : ∀ a, 1 ≤ g a) {a₀ : α} (h₀ : 2 ≤ g a₀) : Fintype.card α + 1 ≤ ∑ a, g a := by
  have h₁ : ∑ a, g a = g a₀ + ∑ a ∈ Finset.univ.erase a₀, g a := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ a₀)]
  rw [h₁]
  have h₂ : ∑ a ∈ Finset.univ.erase a₀, g a ≥ Fintype.card α - 1 := by
    calc ∑ a ∈ Finset.univ.erase a₀, g a ≥ ∑ _a ∈ Finset.univ.erase a₀, 1 :=
           Finset.sum_le_sum fun a _ => h a
      _ = (Finset.univ.erase a₀).card := by simp
      _ = Fintype.card α - 1 := by simp [Finset.card_erase_of_mem (Finset.mem_univ a₀)]
  omega



/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}














variable {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Italian domination number of `K_{m,n}` -/


variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}








open RomanDomination in
theorem solution(h : ∀ i, f (Sum.inl i) ≠ 0) {i₀ : Fin m} (h₀ : f (Sum.inl i₀) = 2) :
    m + 1 ≤ ∑ i, f (Sum.inl i) := by
  have := card_succ_le_sum_of_one_le_of_two (fun i => Nat.pos_of_ne_zero (h i)) h₀.ge
  rwa [Fintype.card_fin] at this
