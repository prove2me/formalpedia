-- Prove2me | solution 1 for RomanDomination.isDRDF_swap
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:41:46.465797+00:00
-- url     : https://prove2.me/submissions/5aa426e4-8ef4-4ce1-9c74-146bdd114902

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





/-! ### The general lower bound `3 ≤ γ_dR(G)` -/


variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj]







/-! ### Local consequences of the double Roman conditions on `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}














/-! ### Explicit double Roman dominating functions of `K_{m,n}` -/


variable {m n : ℕ}











/-! ### Lower bounds for `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### Exact values -/


variable {m n : ℕ}










open RomanDomination in
theorem solution{f : Fin m ⊕ Fin n → ℕ} (hf : IsDRDF (K m n) f) :
    IsDRDF (K n m) (fun x => f x.swap) := by
  have K_adj_swap : ∀ x y : Fin m ⊕ Fin n, (K m n).Adj x y ↔ (K n m).Adj x.swap y.swap := by
    intros; cases ‹Fin m ⊕ Fin n› <;> cases ‹Fin m ⊕ Fin n› <;> simp [K]
  obtain ⟨hbound, hzero, hone⟩ := hf
  refine ⟨fun v => hbound _, fun v hv => ?_, fun v hv => ?_⟩
  · simp only at hv
    rcases hzero (v.swap) hv with h3 | ⟨u, w, hne, hu, hw, hu2, hw2⟩
    · obtain ⟨u', hadj, hu'⟩ := h3
      refine Or.inl ⟨u'.swap, ?_, by simp [hu']⟩
      rw [K_adj_swap] at hadj; simpa only [Sum.swap_swap] using hadj
    · refine Or.inr ⟨u.swap, w.swap, ?_, ?_, ?_, by simp [hu2], by simp [hw2]⟩
      · intro h; apply hne; cases u <;> cases w <;> simp at h <;> cases h <;> trivial
      · rw [K_adj_swap] at hu; simpa only [Sum.swap_swap] using hu
      · rw [K_adj_swap] at hw; simpa only [Sum.swap_swap] using hw
  · simp only at hv
    obtain ⟨u, hadj, hu⟩ := hone (v.swap) hv
    refine ⟨u.swap, ?_, by simp [hu]⟩
    rw [K_adj_swap] at hadj; simpa only [Sum.swap_swap] using hadj
