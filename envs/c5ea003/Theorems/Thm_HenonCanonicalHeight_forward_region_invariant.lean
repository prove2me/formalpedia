-- Prove2me | Theorems.Thm_HenonCanonicalHeight_forward_region_invariant
-- name    : HenonCanonicalHeight.forward_region_invariant
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-10T23:49:14.897895+00:00
-- url     : https://prove2.me/theorems/7c8e54a5-c540-479a-bada-e18450a53b17
-- title:
--   The strengthened forward escape region is invariant under `henon`.
-- statement:
--   The strengthened forward escape region is invariant under `henon`.
--
--   ```lean
--   theorem HenonCanonicalHeight.forward_region_invariant{D : ℕ} (hD : 2 ≤ D) {b : ℝ} {P : ℝ × ℝ}
--       (hP : InForwardRegion D b P) :
--       InForwardRegion D b (henon D b P) := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Bridges/HenonCanonicalHeight.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Bridges/HenonCanonicalHeight.lean#L84

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

theorem HenonCanonicalHeight.forward_region_invariant{D : ℕ} (hD : 2 ≤ D) {b : ℝ} {P : ℝ × ℝ}
    (hP : InForwardRegion D b P) :
    InForwardRegion D b (henon D b P) := by sorry
