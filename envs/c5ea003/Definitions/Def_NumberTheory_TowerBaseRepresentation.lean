-- Prove2me | Definitions.Def_NumberTheory_TowerBaseRepresentation
-- name    : NumberTheory_TowerBaseRepresentation
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:18:34.089866+00:00
-- url     : https://prove2.me/theorems/1dbce469-c9c2-42ba-a5d6-3cfd32fdf65a
-- title:
--   Aether Catalog definitions — NumberTheory_TowerBaseRepresentation
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.TowerBaseRepresentation`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/TowerBaseRepresentation.lean by skeleton subtraction
import Mathlib
import Definitions.Def_NumberTheory_RecursiveMixedRadix

/-!
# Tower-base representations

At position `k` the radix is `2^(towerWeight k)`.  Thus the alphabet itself grows
recursively.  This gives very few *digit positions*, but each high-position digit
comes from an enormous alphabet; the final theorem records the corresponding
bit-cost bound and prevents interpreting position count alone as compression.
-/

namespace TowerBaseRepresentation

open RecursiveMixedRadix

/-- Recursive place values for the tower-base system. -/
def towerWeight : ℕ → ℕ
  | 0 => 1
  | k + 1 => 2 ^ towerWeight k * towerWeight k

/-- The radix available at position `k`. -/
def towerRadix (k : ℕ) : ℕ := 2 ^ towerWeight k





/-- Canonical tower-base digits. -/
def digit (n i : ℕ) : ℕ := RecursiveMixedRadix.digit towerRadix n i

/-- Value of a finite tower-base digit string. -/
def value (c : ℕ → ℕ) (k : ℕ) : ℕ :=
  RecursiveMixedRadix.value towerRadix c k

/-- Validity of a finite tower-base digit string. -/
def Valid (c : ℕ → ℕ) (k : ℕ) : Prop :=
  RecursiveMixedRadix.Valid towerRadix c k




end TowerBaseRepresentation


