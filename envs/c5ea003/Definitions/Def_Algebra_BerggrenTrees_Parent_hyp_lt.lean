-- Prove2me | Definitions.Def_Algebra_BerggrenTrees_Parent_hyp_lt
-- name    : Algebra_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T08:07:42.367348+00:00
-- url     : https://prove2.me/theorems/304f3b91-5ab1-4ef5-8339-9d30ef02ea8a
-- title:
--   Aether Catalog definitions — Algebra_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

Repaired: the file used seven objects that were never declared anywhere in the
catalog — the Pythagorean predicate `IsPT`, the three inverse Berggren maps
`invB1`, `invB2`, `invB3`, their positivity lemmas and the exclusion lemma
`not_both_neg`.  They are supplied here (the maps are the inverses of the three
Berggren matrices `[[1,-2,2],[2,-1,2],[2,-2,3]]`, `[[1,2,2],[2,1,2],[2,2,3]]`,
`[[-1,2,2],[-2,1,2],[-2,2,3]]`), and `parent_exists` is proved from them.
-/

/-- `IsPT a b c` says that `(a, b, c)` satisfies the Pythagorean equation. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- The inverse of the first Berggren matrix. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)

/-- The inverse of the second Berggren matrix. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- The inverse of the third Berggren matrix. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)


