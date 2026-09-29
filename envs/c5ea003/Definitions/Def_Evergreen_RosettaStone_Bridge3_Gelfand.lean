-- Prove2me | Definitions.Def_Evergreen_RosettaStone_Bridge3_Gelfand
-- name    : Evergreen_RosettaStone_Bridge3_Gelfand
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:38:56.657814+00:00
-- url     : https://prove2.me/theorems/78ed9a9e-6f5d-4fed-97c3-71eccbc84c84
-- title:
--   Aether Catalog definitions — Evergreen_RosettaStone_Bridge3_Gelfand
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.RosettaStone.Bridge3.Gelfand`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/RosettaStone/Bridge3_Gelfand.lean by skeleton subtraction
import Mathlib
/-
  Bridge 3: Gelfand Duality — Commutative C*-algebras ↔ Compact Hausdorff Spaces
  ================================================================================
  Projections (p² = p = p*) correspond to clopen subsets.
-/

namespace RosettaStone.Gelfand

variable {R : Type*} [Ring R]

/-- A projection (idempotent element). -/
structure Projection (R : Type*) [Ring R] where
  val : R
  idem : val * val = val

/-- The complement of a projection is a projection. -/
def Projection.complement (p : Projection R) : Projection R where
  val := 1 - p.val
  idem := by
    have h1 : (1 - p.val) * p.val = 0 := by rw [sub_mul, one_mul, p.idem, sub_self]
    calc (1 - p.val) * (1 - p.val)
        = 1 - p.val - (1 - p.val) * p.val := by rw [mul_sub, mul_one]
      _ = 1 - p.val - 0 := by rw [h1]
      _ = 1 - p.val := by rw [sub_zero]




end RosettaStone.Gelfand


