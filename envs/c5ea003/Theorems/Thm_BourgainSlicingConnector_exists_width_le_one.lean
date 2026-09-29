-- Prove2me | Theorems.Thm_BourgainSlicingConnector_exists_width_le_one
-- name    : BourgainSlicingConnector.exists_width_le_one
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-08T15:18:29.392576+00:00
-- url     : https://prove2.me/theorems/43b80714-9daf-4981-8ff4-901400022f5a
-- title:
--   Finite multiplicative pigeonhole principle: a positive finite family with product
-- statement:
--   Finite multiplicative pigeonhole principle: a positive finite family with product
--   one has a member at most one.
--
--   ```lean
--   theorem BourgainSlicingConnector.exists_width_le_one{n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
--       (hvol : boxVolume a = 1) :
--       ∃ i, a i ≤ 1 := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Shared/BourgainSlicingConnector/BourgainSlicingConnector.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Shared/BourgainSlicingConnector/BourgainSlicingConnector.lean#L39

-- Thm stub generated from Shared/BourgainSlicingConnector/BourgainSlicingConnector.lean
import Mathlib
import Definitions.Def_Shared_BourgainSlicingConnector_BourgainSlicingConnector

/-!
# A finite multiplicative bridge for coordinate slices of unit-volume boxes

For an axis-aligned box with positive side lengths `a i`, its volume is the product
of the side lengths.  Its coordinate section perpendicular to axis `i` has volume
the product of all the other side lengths.  Thus the geometric slicing assertion for
boxes is exactly a finite multiplicative pigeonhole principle.

This is a rigorously proved special case and structural model of Bourgain's slicing
problem; it does not claim the open dimension-free theorem for arbitrary convex bodies.
-/

open BourgainSlicingConnector

theorem BourgainSlicingConnector.exists_width_le_one{n : ℕ} (hn : 0 < n) (a : Fin n → ℝ)
    (hvol : boxVolume a = 1) :
    ∃ i, a i ≤ 1 := by sorry
