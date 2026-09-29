-- Prove2me | Definitions.Def_Tropical_BerggrenTrees_Parent_hyp_lt
-- name    : Tropical_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T08:29:32.286109+00:00
-- url     : https://prove2.me/theorems/d00471a7-565b-46a1-b892-64d7f8c6eedb
-- title:
--   Aether Catalog definitions — Tropical_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Tropical.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Tropical/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-- A (not necessarily primitive) integer Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Inverse of the first Berggren matrix `[[1,-2,2],[2,-1,2],[2,-2,3]]`. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, -2 * a - b + 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the second Berggren matrix `[[1,2,2],[2,1,2],[2,2,3]]`. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the third Berggren matrix `[[-1,2,2],[-2,1,2],[-2,2,3]]`. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2 * b + 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)


