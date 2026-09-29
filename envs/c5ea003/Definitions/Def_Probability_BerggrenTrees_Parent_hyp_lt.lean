-- Prove2me | Definitions.Def_Probability_BerggrenTrees_Parent_hyp_lt
-- name    : Probability_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:10:35.014097+00:00
-- url     : https://prove2.me/theorems/bdaefb9a-8b7f-49e5-a16c-ea826a22ac45
-- title:
--   Aether Catalog definitions — Probability_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Probability.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Probability/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

The definitions `IsPT`, `invB1`, `invB2`, `invB3` and the auxiliary positivity
lemmas were missing from the auto-generated file; they are supplied here so that
the module compiles.  `invB1`, `invB2`, `invB3` are the inverses of the three
Berggren (Barning–Hall) matrices

```
B1 = [[ 1,-2,2],[ 2,-1,2],[ 2,-2,3]]
B2 = [[ 1, 2,2],[ 2, 1,2],[ 2, 2,3]]
B3 = [[-1, 2,2],[-2, 1,2],[-2, 2,3]]
```

whose third coordinate is in every case the *parent hypotenuse* `3c - 2a - 2b`.
-/

/-- `IsPT a b c` says that `(a, b, c)` satisfies the Pythagorean relation. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Inverse of the first Berggren matrix. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, -2 * a - b + 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the second Berggren matrix. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2 * b - 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the third Berggren matrix. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2 * b + 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)


