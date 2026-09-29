-- Prove2me | Definitions.Def_Cryptography_BerggrenTrees_Parent_hyp_lt
-- name    : Cryptography_BerggrenTrees_Parent_hyp_lt
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-12T02:11:53.571335+00:00
-- url     : https://prove2.me/theorems/7ffe8e26-8a1f-4960-8ae2-83624837fa14
-- title:
--   Aether Catalog definitions — Cryptography_BerggrenTrees_Parent_hyp_lt
-- statement:
--   Definition bundle for the Aether Catalog module `Cryptography.BerggrenTrees.Parent.hyp.lt`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Cryptography/BerggrenTrees/Parent_hyp_lt.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Shared.Parent_hyp_lt

Auto-generated from theorem catalog database.
Domain: Shared
Declarations: 3
-/


/-- `(a, b, c)` is a Pythagorean triple. -/
def IsPT (a b c : ℤ) : Prop := a ^ 2 + b ^ 2 = c ^ 2

/-- The inverse of the first Berggren matrix, acting on a triple. -/
def invB1 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)

/-- The inverse of the second Berggren matrix, acting on a triple. -/
def invB2 (a b c : ℤ) : ℤ × ℤ × ℤ := (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)

/-- The inverse of the third Berggren matrix, acting on a triple. -/
def invB3 (a b c : ℤ) : ℤ × ℤ × ℤ := (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)


