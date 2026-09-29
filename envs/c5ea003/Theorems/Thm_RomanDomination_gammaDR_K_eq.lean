-- Prove2me | Theorems.Thm_RomanDomination_gammaDR_K_eq
-- name    : RomanDomination.gammaDR_K_eq
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:43:30.215595+00:00
-- url     : https://prove2.me/theorems/4f609823-0910-4a8b-a17c-553cceb2314c
-- title:
--   The double Roman domination number of the complete bipartite graph.
-- statement:
--   **The double Roman domination number of the complete bipartite graph.**
--   With `k = min m n` it equals `3` if `k = 1`, `4` if `k = 2`, and `6` if `k ≥ 3`.
--
--   ```lean
--   theorem RomanDomination.gammaDR_K_eq(hm : 1 ≤ m) (hn : 1 ≤ n) :
--       gammaDR (K m n) = if min m n = 1 then 3 else if min m n = 2 then 4 else 6 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/DoubleRoman.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/DoubleRoman.lean#L679

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







/-! ### Local consequences of the double Roman conditions on `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}














/-! ### Explicit double Roman dominating functions of `K_{m,n}` -/


variable {m n : ℕ}











/-! ### Lower bounds for `K_{m,n}` -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}








/-! ### Exact values -/


variable {m n : ℕ}

theorem RomanDomination.gammaDR_K_eq(hm : 1 ≤ m) (hn : 1 ≤ n) :
    gammaDR (K m n) = if min m n = 1 then 3 else if min m n = 2 then 4 else 6 := by sorry
