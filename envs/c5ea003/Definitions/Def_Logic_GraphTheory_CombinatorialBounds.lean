-- Prove2me | Definitions.Def_Logic_GraphTheory_CombinatorialBounds
-- name    : Logic_GraphTheory_CombinatorialBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T13:54:24.308062+00:00
-- url     : https://prove2.me/theorems/bc535f7d-12ed-49c6-a5f7-52cf1b2ecb71
-- title:
--   Aether Catalog definitions — Logic_GraphTheory_CombinatorialBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Logic.GraphTheory.CombinatorialBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Logic/GraphTheory/CombinatorialBounds.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Logic.CombinatorialBounds

Auto-generated from theorem catalog database.
Domain: Logic
Declarations: 17
-/


/-- Sum of first k+1 binomial coefficients of n. -/
def binomialPartialSum (n k : ℕ) : ℕ := ∑ i ∈ Finset.range (k + 1), n.choose i


