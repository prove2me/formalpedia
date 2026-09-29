-- Prove2me | solution 1 for RomanDomination.isRDF_leftHeavy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:45:26.375195+00:00
-- url     : https://prove2.me/submissions/5e9f7fe9-28c7-48e5-a96c-1d03a4aded92

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








/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}














variable {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Italian domination number of `K_{m,n}` -/


variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}








open RomanDomination in
theorem solution(hm : 1 ≤ m) : IsRDF (K m n) (leftHeavy m n) := by
  constructor
  · -- all values ≤ 2
    intro v
    unfold leftHeavy
    cases v <;> (simp; try (split_ifs <;> norm_num))
  · -- every 0-vertex is adjacent to a 2-vertex
    intro v hv
    unfold leftHeavy at hv
    cases v with
    | inl i =>
      simp at hv
      split_ifs at hv
    | inr j =>
      refine ⟨Sum.inl ⟨0, hm⟩, ?_, ?_⟩
      · simp [K, completeBipartiteGraph_adj]
      · unfold leftHeavy; simp
