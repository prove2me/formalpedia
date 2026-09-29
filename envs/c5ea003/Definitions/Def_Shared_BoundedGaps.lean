-- Prove2me | Definitions.Def_Shared_BoundedGaps
-- name    : Shared_BoundedGaps
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-08T07:34:31.314832+00:00
-- url     : https://prove2.me/theorems/350d5478-f902-4546-b55b-da761e113d96
-- title:
--   Aether Catalog definitions — Shared_BoundedGaps
-- statement:
--   Definition bundle for the Aether Catalog module `Shared.BoundedGaps`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Shared/BoundedGaps.lean by skeleton subtraction
import Mathlib

/-! # Consecutive prime gaps

This file supplies the arithmetic gap observable used by the persistent-homology
formalization of the prime point cloud.
-/

namespace TwinPrimeGaps

/-- The gap between the `n`-th prime and its successor. -/
noncomputable def primeGap (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime (n + 1) - Nat.nth Nat.Prime n




end TwinPrimeGaps


