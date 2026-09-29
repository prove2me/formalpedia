-- Prove2me | Definitions.Def_Speculative_NumberTheory_BerggrenDescentComplete
-- name    : Speculative_NumberTheory_BerggrenDescentComplete
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:32:57.816491+00:00
-- url     : https://prove2.me/theorems/a039d166-1de2-4ead-9501-2fa5c930505d
-- title:
--   Aether Catalog definitions — Speculative_NumberTheory_BerggrenDescentComplete
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.NumberTheory.BerggrenDescentComplete`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/NumberTheory/BerggrenDescentComplete.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Speculative.BerggrenDescentComplete

Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 32
-/

/-- [Section: # CatalogBuild.Speculative.BerggrenDescentComplete
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 32] -/
inductive BerggrenStep' | A | B | C
  deriving DecidableEq

/-- [Section: # CatalogBuild.Speculative.BerggrenDescentComplete
Auto-generated from theorem catalog database.
Domain: Speculative
Declarations: 32] -/
def childTriple' : BerggrenStep' → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | .A, (a, b, c) => (a - 2*b + 2*c, 2*a - b + 2*c, 2*a - 2*b + 3*c)
  | .B, (a, b, c) => (a + 2*b + 2*c, 2*a + b + 2*c, 2*a + 2*b + 3*c)
  | .C, (a, b, c) => (-a + 2*b + 2*c, -2*a + b + 2*c, -2*a + 2*b + 3*c)

def parentTriple' : BerggrenStep' → ℤ × ℤ × ℤ → ℤ × ℤ × ℤ
  | .A, (a, b, c) => (a + 2*b - 2*c, -2*a - b + 2*c, -2*a - 2*b + 3*c)
  | .B, (a, b, c) => (a + 2*b - 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)
  | .C, (a, b, c) => (-a - 2*b + 2*c, 2*a + b - 2*c, -2*a - 2*b + 3*c)
















def sigma1' (a b c : ℤ) : ℤ := a + 2*b - 2*c

def sigma2' (a b c : ℤ) : ℤ := 2*a + b - 2*c


