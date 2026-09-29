-- Prove2me | solution 1 for RomanDomination.weight_cornerTwo
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:48:08.928866+00:00
-- url     : https://prove2.me/submissions/c8b9ba8d-e25e-4068-9bad-6a06d570b4ec

-- Sol generated from Geometry/RomanDomination/ConvexBipartite.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
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








/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Roman domination number of `K_{m,n}` -/


variable {m n : ℕ}














variable {f : Fin m ⊕ Fin n → ℕ}








/-! ### The Italian domination number of `K_{m,n}` -/


variable {m n : ℕ}




variable {f : Fin m ⊕ Fin n → ℕ}








open RomanDomination in
theorem solution(hm : 1 ≤ m) (hn : 1 ≤ n) : weight (cornerTwo m n) = 4 := by
  unfold cornerTwo
  rw [weight_sum_type]
  have left_sum : ∑ i : Fin m, (if i.val = 0 then 2 else 0) = 2 := by
    rw [Finset.sum_ite]
    simp [Finset.sum_const, smul_eq_mul]
    have h1 : #{x : Fin m | (x : ℕ) = 0} = 1 := by
      rw [Finset.card_eq_one]
      use ⟨0, hm⟩
      ext x
      simp [Fin.ext_iff]
    omega
  have right_sum : ∑ j : Fin n, (if j.val = 0 then 2 else 0) = 2 := by
    rw [Finset.sum_ite]
    simp [Finset.sum_const, smul_eq_mul]
    have h1 : #{x : Fin n | (x : ℕ) = 0} = 1 := by
      rw [Finset.card_eq_one]
      use ⟨0, hn⟩
      ext x
      simp [Fin.ext_iff]
    omega
  simp_all
