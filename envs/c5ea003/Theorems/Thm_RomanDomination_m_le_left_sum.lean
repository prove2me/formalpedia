-- Prove2me | Theorems.Thm_RomanDomination_m_le_left_sum
-- name    : RomanDomination.m_le_left_sum
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:42:28.165923+00:00
-- url     : https://prove2.me/theorems/d39ca568-82a2-4edf-9483-f42756842631
-- title:
--   If no left vertex is labelled `0`, the left side weight is at least `m`.
-- statement:
--   If no left vertex is labelled `0`, the left side weight is at least `m`.
--
--   ```lean
--   theorem RomanDomination.m_le_left_sum(h : ∀ i, f (Sum.inl i) ≠ 0) : m ≤ ∑ i, f (Sum.inl i) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/RomanDomination/ConvexBipartite.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/RomanDomination/ConvexBipartite.lean#L178

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





variable (m n)



/-! ### Splitting weights over the two sides -/


variable {m n : ℕ}








/-! ### Roman dominating functions of `K_{m,n}`: structure -/


variable {m n : ℕ} {f : Fin m ⊕ Fin n → ℕ}

theorem RomanDomination.m_le_left_sum(h : ∀ i, f (Sum.inl i) ≠ 0) : m ≤ ∑ i, f (Sum.inl i) := by sorry
