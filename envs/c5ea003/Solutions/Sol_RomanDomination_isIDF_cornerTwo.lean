-- Prove2me | solution 1 for RomanDomination.isIDF_cornerTwo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:26.54714+00:00
-- url     : https://prove2.me/submissions/3fb039df-57f3-4442-9b47-4139ce877e65

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








open RomanDomination in
theorem solution(hm : 1 ≤ m) (hn : 1 ≤ n) : IsIDF (K m n) (cornerTwo m n) := by
  constructor
  · -- all values ≤ 2
    intro v
    unfold cornerTwo
    cases v <;> (simp; try (split_ifs <;> norm_num))
  · -- every 0-vertex has neighbor sum ≥ 2
    intro v hv
    unfold cornerTwo at hv
    cases v with
    | inl i =>
      simp at hv
      rw [K_neighbor_sum_inl]
      simp [cornerTwo]
      rw [Finset.sum_ite]
      simp [Finset.sum_const, smul_eq_mul]
      exact ⟨⟨0, hn⟩, by simp⟩
    | inr j =>
      simp at hv
      rw [K_neighbor_sum_inr]
      simp [cornerTwo]
      rw [Finset.sum_ite]
      simp [Finset.sum_const, smul_eq_mul]
      exact ⟨⟨0, hm⟩, by simp⟩
