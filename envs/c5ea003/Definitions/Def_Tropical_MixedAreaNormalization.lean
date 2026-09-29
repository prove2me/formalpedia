-- Prove2me | Definitions.Def_Tropical_MixedAreaNormalization
-- name    : Tropical_MixedAreaNormalization
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:32:11.054197+00:00
-- url     : https://prove2.me/theorems/291a9996-7bef-4ccc-8ddc-887ac7f68896
-- title:
--   Aether Catalog definitions — Tropical_MixedAreaNormalization
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.MixedAreaNormalization`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/MixedAreaNormalization.lean by skeleton subtraction
import Mathlib

/-!
# Normalization in the plane tropical Bézout formula

For the standard lattice triangle dilated by a natural degree `d`, normalized
lattice area is `d²` when the primitive lattice triangle has area one.  This
file computes the corresponding polarization exactly.  The result exposes a
factor of two: the raw difference of normalized areas is `2de`, whereas the
Bézout intersection number is `de`.
-/

namespace TropicalMixedArea

/-- Normalized lattice area of the degree-`d` standard Newton triangle. -/
def normalizedTriangleArea (d : ℕ) : ℤ := (d : ℤ) ^ 2

/-- The raw area polarization for two standard Newton triangles. -/
def normalizedMixedAreaDifference (d e : ℕ) : ℤ :=
  normalizedTriangleArea (d + e) - normalizedTriangleArea d -
    normalizedTriangleArea e







end TropicalMixedArea


