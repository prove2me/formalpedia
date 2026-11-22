-- Prove2me | Theorems.Thm_Matrix_coeffs_sup_transpose
-- name    : Matrix.coeffs_sup_transpose
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:25.723016+00:00
-- url     : https://prove2.me/theorems/1c1b4f5f-a194-4083-9a89-4e1daa126361
-- title:
--   Matrix: coeffs sup transpose
-- statement:
--   The supremum of the coefficients is invariant under transposition.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L187-L189
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L187-L189

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable {Γ₀ : Type*} [LinearOrderedCommMonoidWithZero Γ₀] (v : Valuation R Γ₀)
variable [Finite n] [Finite m] [Finite n'] [Finite m'] [Nonempty n] [Nonempty m]
  [Nonempty n'] [Nonempty m']

theorem Matrix.coeffs_sup_transpose (g : Matrix n m R) :
    g.transpose.coeffs_sup v = g.coeffs_sup v := by sorry
