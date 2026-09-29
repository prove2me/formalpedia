-- Prove2me | Theorems.Thm_RomanDomination_min_succ_le_weight_of_isURRDF_K
-- name    : RomanDomination.min_succ_le_weight_of_isURRDF_K
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:25.871713+00:00
-- url     : https://prove2.me/theorems/0c32a6a0-047f-4171-9512-aaa50bef17dd
-- title:
--   Every unique response Roman dominating function of `K_{m,n}` has weight at least
-- statement:
--   Every unique response Roman dominating function of `K_{m,n}` has weight at least
--   `min (m+1) (n+1)`.  (Only `m ≥ 1` is needed.)
--
--   ```lean
--   theorem RomanDomination.min_succ_le_weight_of_isURRDF_K(hm : 1 ≤ m) (hf : IsURRDF (K m n) f) :
--       min (m + 1) (n + 1) ≤ weight f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/PerfectUnique.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/PerfectUnique.lean#L212

-- Thm stub generated from Geometry/RomanDomination/PerfectUnique.lean
import Mathlib
import Definitions.Def_Geometry_RomanDomination_ConvexBipartite
import Definitions.Def_Geometry_RomanDomination_Variants
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

theorem RomanDomination.min_succ_le_weight_of_isURRDF_K(hm : 1 ≤ m) (hf : IsURRDF (K m n) f) :
    min (m + 1) (n + 1) ≤ weight f := by sorry
