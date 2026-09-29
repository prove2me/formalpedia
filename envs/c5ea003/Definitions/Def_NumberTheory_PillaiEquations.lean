-- Prove2me | Definitions.Def_NumberTheory_PillaiEquations
-- name    : NumberTheory_PillaiEquations
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-10T13:09:44.197068+00:00
-- url     : https://prove2.me/theorems/819e0d97-b95a-4978-a225-d5746b62f8e1
-- title:
--   Aether Catalog definitions — NumberTheory_PillaiEquations
-- statement:
--   Definition bundle for the Aether Catalog module `NumberTheory.PillaiEquations`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from NumberTheory/PillaiEquations.lean by skeleton subtraction
import Mathlib

/-!
# Elementary Structure of Pillai Equations

This file develops reusable facts about equations of the form
`x ^ a = y ^ b + k`.  It proves divisibility and coprimality constraints,
shows how composite exponents reduce to smaller exponents, and gives an
exact classification of the small square-cube search region
`1 ≤ k ≤ 10`, `2 ≤ x,y ≤ 20`.
-/

namespace PillaiEquations

/-- `PillaiSolution k x y a b` means that the two perfect powers differ by
exactly `k`, with the power of `x` the larger one. -/
def PillaiSolution (k x y a b : ℕ) : Prop :=
  x ^ a = y ^ b + k










end PillaiEquations


