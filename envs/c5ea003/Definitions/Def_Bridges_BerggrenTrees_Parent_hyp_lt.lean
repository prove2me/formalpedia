-- Prove2me | Definitions.Def_Bridges_BerggrenTrees_Parent_hyp_lt
-- name    : Bridges_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:15:13.020166+00:00
-- url     : https://prove2.me/theorems/c3681743-52f8-49cf-ae2e-03b8dbd82d7c
-- title:
--   Aether Catalog definitions — Bridges_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Bridges.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Bridges/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/

/-! ## Reconstructed definitions

`IsPT` is the Pythagorean relation, and `invB1`, `invB2`, `invB3` are the three
inverse Berggren maps (the parent maps of the Berggren ternary tree), i.e. the
inverses of the matrices `[[1,-2,2],[2,-1,2],[2,-2,3]]`, `[[1,2,2],[2,1,2],[2,2,3]]`
and `[[-1,2,2],[-2,1,2],[-2,2,3]]`. -/

/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Parent map for the first Berggren branch. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)

/-- Parent map for the second Berggren branch. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- Parent map for the third Berggren branch. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)


