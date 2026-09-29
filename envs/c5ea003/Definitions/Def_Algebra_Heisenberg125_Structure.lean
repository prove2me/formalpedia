-- Prove2me | Definitions.Def_Algebra_Heisenberg125_Structure
-- name    : Algebra_Heisenberg125_Structure
-- status  : Definition
-- author  : @raver1975
-- created : 2026-09-17T16:33:11.539361+00:00
-- url     : https://prove2.me/theorems/c340e0cc-be81-4ea2-867b-b02f74e72209
-- title:
--   Aether Catalog definitions — Algebra_Heisenberg125_Structure
-- statement:
--   Definition bundle for the Aether Catalog module `Algebra.Heisenberg125.Structure`, transplanted by skeleton subtraction; supplies the types and constants the catalog's theorems import.

-- Def bundle generated from Algebra/Heisenberg125/Structure.lean by skeleton subtraction
import Mathlib
import Definitions.Def_Algebra_Heisenberg125_Basic
/-
# Structure of `H_{p^3}`: matrix realisation, centre, commutator subgroup, exponent

This file justifies the description of `Heis p` used throughout: it *is* the
group of upper unitriangular `3 × 3` matrices over `ZMod p`, its centre and
commutator subgroup both equal `⟨v⟩ ≅ C_p`, it has order `p ^ 3` (so
`|Heis 5| = 125`) and, for odd primes `p`, exponent exactly `p`.
-/

namespace Heisenberg125

namespace Heis

variable {p : ℕ}

/-! ## Matrix realisation -/

/-- The unitriangular matrix attached to an element of `Heis p`. -/
def toMatrix (g : Heis p) : Matrix (Fin 3) (Fin 3) (ZMod p) :=
  !![1, g.a, g.c; 0, 1, g.b; 0, 0, 1]

/-- `Heis p` is the group of upper unitriangular `3 × 3` matrices over
`ZMod p`: the map `toMatrix` is a multiplicative, injective map. -/
def toMatrixHom : Heis p →* Matrix (Fin 3) (Fin 3) (ZMod p) where
  toFun := toMatrix
  map_one' := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [toMatrix]
  map_mul' g h := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [toMatrix, Matrix.mul_apply, Fin.sum_univ_three] <;> ring


/-! ## Centre and commutator subgroup -/





/-! ## Order and exponent -/




end Heis

end Heisenberg125


