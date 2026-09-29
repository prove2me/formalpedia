-- Prove2me | Theorems.Thm_no_finite_subcover_Iio_of_noMax
-- name    : no_finite_subcover_Iio_of_noMax
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T00:34:29.79371+00:00
-- url     : https://prove2.me/theorems/6adb56c4-8b6a-423f-a89c-4a069c53069d
-- title:
--   No finite collection of initial segments covers an unbounded order.
-- statement:
--   **No finite collection of initial segments covers an unbounded order.**
--   Given a finite set `S` of elements in a linear order with no maximum, the cover
--   `⋃ a ∈ S, Iio a` misses elements above the maximum of `S`.
--
--   *Proof method:* By cases on whether `S` is nonempty; if so, extract the maximum `m`,
--   find `m' > m`, and derive a chain of inequalities leading to `m < m`.
--
--   ```lean
--   theorem no_finite_subcover_Iio_of_noMax    (α : Type*) [LinearOrder α] [NoMaxOrder α]
--       [Nonempty α]
--       (S : Finset α) : ¬ (univ : Set α) ⊆ ⋃ a ∈ S, Iio a := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/PosetTheory/SurrealTopologyExtended.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/PosetTheory/SurrealTopologyExtended.lean#L60

-- Thm stub generated from Bridges/PosetTheory/SurrealTopologyExtended.lean
import Mathlib
import Definitions.Def_Bridges_PosetTheory_SurrealTopologyExtended

open Set TopologicalSpace Filter

/-! # Surreal Topology: Open Sets at Infinity

This file extends the topological theory of ordered continua motivated by Conway's
surreal numbers. We prove:

1. **Unbounded ordered topological spaces are noncompact** via explicit open covers.
2. **Uncountable coinitiality obstructs countable bases** above a point.
3. **Open set extension via order embeddings** is always open.
4. **Hausdorff, connectedness, and separation** results for order topologies.
5. **Order-convex sets** are closed under intersections and monotone preimages.

## Novel Definitions

* `UncountableUpperCoinitiality` — captures the coinitiality gap structure at a point,
  abstracting the key property that makes surreal numbers topologically exotic.
* `SurrealOpenExtension` — canonical extension of an open set from a sub-order
  to the ambient order via an order embedding.

## References

* J.H. Conway, *On Numbers and Games*, Academic Press, 1976.
* P. Ehrlich, *Bulletin of Symbolic Logic*, 2012.
-/

/-! ## Novel Definitions -/





/-! ## Theorem 1: Finite Initial-Segment Covers Fail for Unbounded Orders -/

theorem no_finite_subcover_Iio_of_noMax    (α : Type*) [LinearOrder α] [NoMaxOrder α]
    [Nonempty α]
    (S : Finset α) : ¬ (univ : Set α) ⊆ ⋃ a ∈ S, Iio a := by sorry
