-- Prove2me | Theorems.Thm_RomanDomination_K_not_adj_inl_inl
-- name    : RomanDomination.K_not_adj_inl_inl
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:41:56.191015+00:00
-- url     : https://prove2.me/theorems/69d4cc47-198d-42f4-8266-cd06e733735c
-- title:
--   K not adj inl inl
-- statement:
--   Formal statement of `RomanDomination.K_not_adj_inl_inl` from the Aether Catalog (Geometry). The mathematical content is given by the Lean statement below; a human-readable write-up is pending.
--
--   ```lean
--   theorem RomanDomination.K_not_adj_inl_inl(i i' : Fin m) : ¬ (K m n).Adj (Sum.inl i) (Sum.inl i') := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/ConvexBipartite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/ConvexBipartite.lean#L74

-- Thm stub generated from Geometry/RomanDomination/ConvexBipartite.lean
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

theorem RomanDomination.K_not_adj_inl_inl(i i' : Fin m) : ¬ (K m n).Adj (Sum.inl i) (Sum.inl i') := by sorry
