-- Prove2me | solution 1 for RomanDomination.gammaR_K
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:16.714841+00:00
-- url     : https://prove2.me/submissions/ed7097fb-f655-4643-a99e-db866b3e548a

-- Sol generated from Geometry/RomanDomination/ConvexBipartite.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_gammaR_le
import Theorems.Thm_RomanDomination_isRDF_cornerTwo
import Theorems.Thm_RomanDomination_isRDF_leftHeavy
import Theorems.Thm_RomanDomination_isRDF_rightHeavy
import Theorems.Thm_RomanDomination_le_gammaR
import Theorems.Thm_RomanDomination_min_le_weight_of_isRDF_K
import Theorems.Thm_RomanDomination_weight_cornerTwo
import Theorems.Thm_RomanDomination_weight_leftHeavy
import Theorems.Thm_RomanDomination_weight_rightHeavy
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
theorem solution(hm : 1 ≤ m) (hn : 1 ≤ n) :
    gammaR (K m n) = min 4 (min (m + 1) (n + 1)) := by
  refine le_antisymm (le_min ?_ (le_min ?_ ?_))
    (le_gammaR _ fun f hf => min_le_weight_of_isRDF_K hm hn hf)
  · exact (gammaR_le _ (isRDF_cornerTwo hm hn)).trans_eq (weight_cornerTwo hm hn)
  · exact (gammaR_le _ (isRDF_leftHeavy hm)).trans_eq (weight_leftHeavy hm)
  · exact (gammaR_le _ (isRDF_rightHeavy hn)).trans_eq (weight_rightHeavy hn)
