-- Prove2me | solution 1 for RomanDomination.isURRDF_leftHeavy
-- status  : ACCEPTED   (prove)
-- author  : @raver1975
-- created : 2026-09-11T20:50:37.470223+00:00
-- url     : https://prove2.me/submissions/1048d623-1292-4c5d-8f80-e7694f684ee2

-- Sol generated from Geometry/RomanDomination/PerfectUnique.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
import Theorems.Thm_RomanDomination_K_adj_inr_inl
import Theorems.Thm_RomanDomination_K_not_adj_inl_inl
import Theorems.Thm_RomanDomination_K_not_adj_inr_inr
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










open RomanDomination in
theorem solution(hm : 1 ≤ m) : IsURRDF (K m n) (leftHeavy m n) := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    cases v <;> (simp [leftHeavy]; try (split_ifs <;> norm_num))
  · intro v hv
    cases v with
    | inl i =>
      exfalso
      simp only [leftHeavy, Sum.elim_inl] at hv
      split_ifs at hv
    | inr j =>
      refine ⟨Sum.inl ⟨0, hm⟩, ⟨K_adj_inr_inl j _, by simp [leftHeavy]⟩, ?_⟩
      rintro (u | u) ⟨hadj, hu⟩
      · simp only [leftHeavy, Sum.elim_inl] at hu
        have : (u : ℕ) = 0 := by by_contra h; simp [h] at hu
        simp [Fin.ext_iff, this]
      · exact absurd hadj (K_not_adj_inr_inr j u)
  · intro v hv u hadj
    cases v with
    | inl i =>
      cases u with
      | inl i' => exact absurd hadj (K_not_adj_inl_inl i i')
      | inr j => simp [leftHeavy]
    | inr j =>
      exfalso
      simp only [leftHeavy, Sum.elim_inr] at hv
      omega
