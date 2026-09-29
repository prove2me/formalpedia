-- Prove2me | solution 1 for RomanDomination.three_le_weight_of_isDRDF
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:43:53.18073+00:00
-- url     : https://prove2.me/submissions/9082ffca-a8d4-4ace-8fd4-a658b1153ae4

-- Sol generated from Geometry/RomanDomination/DoubleRoman.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_DoubleRoman
import Definitions.Def_Geometry_RomanDomination_Variants
/-
# The double Roman domination number of the complete bipartite graph

This file computes `γ_dR(K_{m,n})` exactly for all `m, n ≥ 1`.  Writing
`k = min m n`, the answer is

```
γ_dR(K_{m,n}) = 3   if k = 1,
              = 4   if k = 2,
              = 6   if k ≥ 3.
```

Note that this is *not* of the shape `min 6 (k + 2)`: the value jumps from `4`
to `6`, skipping `5`.

The lower bounds are obtained from the local conditions defining a double Roman
dominating function, applied to a `0`-labelled vertex on each side; the upper
bounds come from three explicit labellings (`3` on the unique left vertex,
`2` on both left vertices, and `3` on one vertex of each side).

Along the way we prove the general bound `3 ≤ γ_dR(G)` for every graph with at
least two vertices.
-/


open RomanDomination

open Finset

/-! ### General weight plumbing -/


variable {α : Type*} [Fintype α] [DecidableEq α] {g : α → ℕ}

/-- Two distinct values bound the sum from below. -/
lemma pair_le_sum {a b : α} (hab : a ≠ b) : g a + g b ≤ ∑ x, g x := by
  rw [← Finset.sum_pair hab]
  exact Finset.sum_le_sum_of_subset (Finset.subset_univ _)




/-! ### The general lower bound `3 ≤ γ_dR(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]

omit [DecidableEq V] [DecidableRel G.Adj] in
/-- A single value bounds the weight from below. -/
lemma le_weight_single (f : V → ℕ) (v : V) : f v ≤ weight f :=
  Finset.single_le_sum (f := f) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)

omit [DecidableRel G.Adj] in
/-- Two distinct values bound the weight from below. -/
lemma pair_le_weight (f : V → ℕ) {u v : V} (h : u ≠ v) : f u + f v ≤ weight f :=
  pair_le_sum h





/-! ### Local consequences of the double Roman conditions on `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}














/-! ### Explicit double Roman dominating functions of `K_{m,n}` -/


variable {m n : ℕ}











/-! ### Lower bounds for `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### Exact values -/


variable {m n : ℕ}










open RomanDomination in
omit [DecidableRel G.Adj] in
theorem solution(hV : 2 ≤ Fintype.card V) {f : V → ℕ} (hf : IsDRDF G f) :
    3 ≤ weight f := by
  have hbound := hf.1
  by_cases hex : ∃ v, f v ≥ 3
  · obtain ⟨v, hv⟩ := hex; exact le_trans hv (le_weight_single f v)
  · push_neg at hex
    -- All values are 0, 1, or 2
    have h0 := hf.2.1
    have h1 := hf.2.2
    by_cases hzero : ∃ v, f v = 0
    · -- There's a 0-vertex, which needs two ≥2 neighbours
      obtain ⟨v, hv⟩ := hzero
      have := h0 v hv
      rcases this with ⟨u, _, hu⟩ | ⟨u, w, hne, huv, hvw, hu, hw⟩
      · linarith [hex u]
      · exact le_trans (by omega : 3 ≤ f u + f w) (pair_le_weight f hne)
    · -- No vertex is labelled 0, so all are 1 or 2
      push_neg at hzero
      by_cases hone : ∃ v, f v = 1
      · -- There's a 1-vertex, which needs a ≥2 neighbour
        obtain ⟨v, hv⟩ := hone
        obtain ⟨u, huv, hu⟩ := h1 v hv
        -- v and u are distinct (adjacent), f v = 1, f u ≥ 2
        have hu_ne_v : u ≠ v := huv.ne.symm
        exact le_trans (by omega : 3 ≤ f u + f v) (pair_le_weight f hu_ne_v)
      · -- All vertices are labelled 2
        push_neg at hone
        -- All values are exactly 2
        have hall : ∀ v, f v = 2 := fun v => by have := hex v; have := hzero v; have := hone v; omega
        have : weight f = 2 * Fintype.card V := by simp [weight, hall]; ring
        linarith
