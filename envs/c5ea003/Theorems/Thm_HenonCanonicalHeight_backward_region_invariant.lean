-- Prove2me | Theorems.Thm_HenonCanonicalHeight_backward_region_invariant
-- name    : HenonCanonicalHeight.backward_region_invariant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:08.302906+00:00
-- url     : https://prove2.me/theorems/ab800233-1f10-43d1-98e3-bb0b2dd7332c
-- title:
--   The strengthened backward escape region is invariant under the inverse map.
-- statement:
--   The strengthened backward escape region is invariant under the inverse map.
--
--   ```lean
--   theorem HenonCanonicalHeight.backward_region_invariant{D : ℕ} (hD : 2 ≤ D) {b : ℝ} {P : ℝ × ℝ}
--       (hP : InBackwardRegion D b P) :
--       InBackwardRegion D b (henonInv D b P) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HenonCanonicalHeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HenonCanonicalHeight.lean#L161

-- Thm stub generated from Bridges/HenonCanonicalHeight.lean
import Mathlib
import Definitions.Def_Bridges_HenonCanonicalHeight

/-!
# Escape regions and normalized heights for a Hénon map

This file formalizes algebraic and analytic ingredients used in the study of the map
`φ(x,y) = (y, x + y^D + b)`.  The escape region below is a slightly strengthened,
robust version of the usual archimedean escape region: the additional condition
`3 |y| < |y|^D` makes forward invariance transparent even in the presence of
cancellation.  No global arithmetic-height machinery is assumed.
-/

open HenonCanonicalHeight

theorem HenonCanonicalHeight.backward_region_invariant{D : ℕ} (hD : 2 ≤ D) {b : ℝ} {P : ℝ × ℝ}
    (hP : InBackwardRegion D b P) :
    InBackwardRegion D b (henonInv D b P) := by sorry
