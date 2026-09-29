-- Prove2me | Definitions.Def_Combinatorics_BerggrenTrees_Parent_hyp_lt
-- name    : Combinatorics_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-11T20:28:20.253586+00:00
-- url     : https://prove2.me/theorems/3a8f003c-9e12-449d-a3c9-df89bcb4557b
-- title:
--   Aether Catalog definitions — Combinatorics_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Combinatorics.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Combinatorics/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3

The three inverse Barning–Hall matrices `invB1`, `invB2`, `invB3`, the predicate
`IsPT`, and the auxiliary positivity lemmas used by `parent_exists` were missing
from the catalog; they are supplied here so that the file elaborates.
-/

/-- `IsPT a b c` says that `(a, b, c)` is a Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- Inverse of the first Barning–Hall matrix
`!![1, -2, 2; 2, -1, 2; 2, -2, 3]`. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2 * b - 2 * c, -2 * a - b + 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the second Barning–Hall matrix
`!![1, 2, 2; 2, 1, 2; 2, 2, 3]`. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (a + 2 * b - 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)

/-- Inverse of the third Barning–Hall matrix
`!![-1, 2, 2; -2, 1, 2; -2, 2, 3]`. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ :=
  (-a - 2 * b + 2 * c, 2 * a + b - 2 * c, -2 * a - 2 * b + 3 * c)


