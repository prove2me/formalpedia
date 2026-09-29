-- Prove2me | Theorems.Thm_CosmicHorrorGeometry_mobius_eq_id_of_fixes_zero_one_infty
-- name    : CosmicHorrorGeometry.mobius_eq_id_of_fixes_zero_one_infty
-- status  : Proved
-- author  : @raver1975
-- created : 2026-09-11T01:10:27.203356+00:00
-- url     : https://prove2.me/theorems/98ad87f9-df65-47d9-a3aa-1af71e53a8a7
-- title:
--   Uniqueness of the normalisation.
-- statement:
--   **Uniqueness of the normalisation.**  A real Möbius transformation fixing
--   the three boundary points `0`, `1` and `∞` is the identity.  Fixing `∞` means
--   having no finite pole, i.e. `C = 0`.
--
--   ```lean
--   theorem CosmicHorrorGeometry.mobius_eq_id_of_fixes_zero_one_infty{A B D : ℝ} (hD : D ≠ 0)
--       (h0 : mobiusR A B 0 D 0 = 0) (h1 : mobiusR A B 0 D 1 = 1) :
--       ∀ x : ℝ, mobiusR A B 0 D x = x := by sorry
--   ```
--
--   **Formalization Note** Transplanted verbatim from the Aether Catalog source `Geometry/CosmicHorror/HalfPlaneMobius.lean`; the statement is byte-identical to the source declaration, elaborated with `autoImplicit` disabled in the platform environment.
-- source:
--   https://github.com/paulklemstine/Lean/blob/53c2925a02/Catalog/Geometry/CosmicHorror/HalfPlaneMobius.lean#L165

-- Thm stub generated from Geometry/CosmicHorror/HalfPlaneMobius.lean
import Mathlib
import Definitions.Def_Geometry_CosmicHorror_HalfPlaneMobius
import Definitions.Def_Geometry_CosmicHorror_HyperbolicIdealArea

/-!
# Boundary triples, real Möbius maps, and normalisation of ideal triangles

`HyperbolicIdealArea.lean` computes the hyperbolic area of the ideal triangle
whose vertices are two finite boundary points `a < b` and the boundary point
`∞`.  To know that this covers *every* ideal triangle one needs the classical
fact that the orientation-preserving isometry group of the half-plane model,
namely the real Möbius group `PSL(2, ℝ)`, acts **sharply three-transitively** on
the boundary circle `ℝ ∪ {∞}`.  This file proves exactly that, in an elementary
and fully explicit form, together with the two facts that make such maps
isometries of the hyperbolic plane:

* `mobius_im`:  `Im T(z) = det · Im z / ‖Cz + D‖²`, so a positive determinant
  forces the upper half-plane to be preserved (`mobius_mapsTo_upperHalfPlane`).
* `mobius_conformal_factor`:  `‖T'(z)‖ / Im T(z) = 1 / Im z`, i.e. `T` preserves
  the hyperbolic line element `|dz| / y` pointwise.  This is the infinitesimal
  statement of "`T` is a hyperbolic isometry".
* `exists_mobius_normalising`:  every triple `p < q < r` of finite boundary
  points is carried to the normal form `(0, 1, ∞)` by a real Möbius map of
  positive determinant, and `mobius_eq_id_of_fixes_zero_one_infty` shows that
  the normalising map is unique.  Hence three distinct boundary points do
  determine an ideal triangle, uniquely up to hyperbolic isometry.
-/

open CosmicHorrorGeometry

open Real Set Filter Topology Complex

/-! ### The real Möbius action -/







/-! ### Sharp three-transitivity on the boundary -/

theorem CosmicHorrorGeometry.mobius_eq_id_of_fixes_zero_one_infty{A B D : ℝ} (hD : D ≠ 0)
    (h0 : mobiusR A B 0 D 0 = 0) (h1 : mobiusR A B 0 D 1 = 1) :
    ∀ x : ℝ, mobiusR A B 0 D x = x := by sorry
