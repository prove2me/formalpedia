-- Prove2me | Definitions.Def_Evergreen_RosettaStone_Bridge5_Noncommutative
-- name    : Evergreen_RosettaStone_Bridge5_Noncommutative
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-13T16:38:57.066972+00:00
-- url     : https://prove2.me/theorems/3b5b64ea-481c-496f-9687-e362cfcf884c
-- title:
--   Aether Catalog definitions — Evergreen_RosettaStone_Bridge5_Noncommutative
-- statement:
--   Definition bundle for the Aether Catalog module `Evergreen.RosettaStone.Bridge5.Noncommutative`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Evergreen/RosettaStone/Bridge5_Noncommutative.lean by skeleton subtraction
import Mathlib
/-
  Bridge 5: Noncommutative Geometry — NC C*-algebras ↔ NC Spaces
  ================================================================
  When multiplication is no longer commutative, the projection lattice
  becomes orthomodular (not Boolean).
-/

namespace RosettaStone.Noncommutative

variable {n : ℕ}

/-- The commutator [A, B] = AB - BA. -/
def commutator (A B : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  A * B - B * A







end RosettaStone.Noncommutative


