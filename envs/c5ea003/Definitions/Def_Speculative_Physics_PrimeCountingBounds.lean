-- Prove2me | Definitions.Def_Speculative_Physics_PrimeCountingBounds
-- name    : Speculative_Physics_PrimeCountingBounds
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T04:34:42.421312+00:00
-- url     : https://prove2.me/theorems/3758964a-5fcd-41c2-9c7a-15a9a692d96e
-- title:
--   Aether Catalog definitions — Speculative_Physics_PrimeCountingBounds
-- statement:
--   Definition bundle for the Aether Catalog module `Speculative.Physics.PrimeCountingBounds`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Speculative/Physics/PrimeCountingBounds.lean by skeleton subtraction
import Mathlib

/-! # CatalogBuild.Physics.PrimeCountingBounds

Auto-generated from theorem catalog database.
Domain: Physics
Declarations: 16
-/

/-- The prime-counting function π(x) = |{p ≤ x : p is prime}|. -/
def primeCount (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter Nat.Prime).card


