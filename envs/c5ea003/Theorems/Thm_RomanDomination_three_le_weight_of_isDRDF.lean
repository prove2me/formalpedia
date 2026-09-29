-- Prove2me | Theorems.Thm_RomanDomination_three_le_weight_of_isDRDF
-- name    : RomanDomination.three_le_weight_of_isDRDF
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:43:37.753977+00:00
-- url     : https://prove2.me/theorems/e8286387-60c6-4cd8-bb5e-0221a6a53b65
-- title:
--   On a graph with at least two vertices, every double Roman dominating function has
-- statement:
--   On a graph with at least two vertices, every double Roman dominating function has
--   weight at least `3`.
--
--   ```lean
--   theorem RomanDomination.three_le_weight_of_isDRDF(hV : 2 ≤ Fintype.card V) {f : V → ℕ} (hf : IsDRDF G f) :
--       3 ≤ weight f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/DoubleRoman.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/DoubleRoman.lean#L82

-- Thm stub generated from Geometry/RomanDomination/DoubleRoman.lean
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



omit [DecidableRel G.Adj] in

theorem RomanDomination.three_le_weight_of_isDRDF(hV : 2 ≤ Fintype.card V) {f : V → ℕ} (hf : IsDRDF G f) :
    3 ≤ weight f := by sorry
