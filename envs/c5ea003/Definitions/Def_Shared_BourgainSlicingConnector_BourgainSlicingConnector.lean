-- Prove2me | Definitions.Def_Shared_BourgainSlicingConnector_BourgainSlicingConnector
-- name    : Shared_BourgainSlicingConnector_BourgainSlicingConnector
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:45.425981+00:00
-- url     : https://prove2.me/theorems/d7b081c9-41f8-414d-ae07-a09d70cc2099
-- title:
--   Aether Catalog definitions — Shared_BourgainSlicingConnector_BourgainSlicingConnector
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.BourgainSlicingConnector.BourgainSlicingConnector`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/BourgainSlicingConnector/BourgainSlicingConnector.lean by skeleton subtraction
import Mathlib

/-!
# A finite multiplicative bridge for coordinate slices of unit-volume boxes

For an axis-aligned box with positive side lengths `a i`, its volume is the product
of the side lengths.  Its coordinate section perpendicular to axis `i` has volume
the product of all the other side lengths.  Thus the geometric slicing assertion for
boxes is exactly a finite multiplicative pigeonhole principle.

This is a rigorously proved special case and structural model of Bourgain's slicing
problem; it does not claim the open dimension-free theorem for arbitrary convex bodies.
-/

namespace BourgainSlicingConnector

/-- The `n`-dimensional volume of an axis-aligned box represented by its side lengths. -/
def boxVolume {n : ℕ} (a : Fin n → ℝ) : ℝ := ∏ i, a i

/-- The `(n-1)`-dimensional volume of the central coordinate section perpendicular to
axis `i`, represented as the product of all side lengths except `a i`. -/
def coordinateSectionVolume {n : ℕ} (a : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∏ j, if j = i then 1 else a j





end BourgainSlicingConnector


