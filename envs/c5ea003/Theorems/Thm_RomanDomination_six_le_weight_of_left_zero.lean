-- Prove2me | Theorems.Thm_RomanDomination_six_le_weight_of_left_zero
-- name    : RomanDomination.six_le_weight_of_left_zero
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:43:18.772926+00:00
-- url     : https://prove2.me/theorems/2e62ee6c-58b6-454e-a1f5-5a4c91a30620
-- title:
--   Branch of the `6`-bound: both side weights are at least `2` and some left vertex is
-- statement:
--   Branch of the `6`-bound: both side weights are at least `2` and some left vertex is
--   labelled `0`.
--
--   ```lean
--   theorem RomanDomination.six_le_weight_of_left_zero(hn : 3 ≤ n) (hf : IsDRDF (K m n) f)
--       (ha : 2 ≤ ∑ i, f (Sum.inl i)) (h0 : ∃ i, f (Sum.inl i) = 0) : 6 ≤ weight f := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/DoubleRoman.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/DoubleRoman.lean#L465

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

theorem RomanDomination.six_le_weight_of_left_zero(hn : 3 ≤ n) (hf : IsDRDF (K m n) f)
    (ha : 2 ≤ ∑ i, f (Sum.inl i)) (h0 : ∃ i, f (Sum.inl i) = 0) : 6 ≤ weight f := by sorry
