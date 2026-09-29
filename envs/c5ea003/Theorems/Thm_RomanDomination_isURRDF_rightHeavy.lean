-- Prove2me | Theorems.Thm_RomanDomination_isURRDF_rightHeavy
-- name    : RomanDomination.isURRDF_rightHeavy
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:48:12.373768+00:00
-- url     : https://prove2.me/theorems/d206ee03-cd42-451f-9d41-e03f49cc277d
-- title:
--   The right-heavy labelling is a unique response Roman dominating function of
-- statement:
--   The right-heavy labelling is a unique response Roman dominating function of
--   `K_{m,n}`.
--
--   ```lean
--   theorem RomanDomination.isURRDF_rightHeavy(hn : 1 ≤ n) : IsURRDF (K m n) (rightHeavy m n) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/PerfectUnique.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/PerfectUnique.lean#L113

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

theorem RomanDomination.isURRDF_rightHeavy(hn : 1 ≤ n) : IsURRDF (K m n) (rightHeavy m n) := by sorry
