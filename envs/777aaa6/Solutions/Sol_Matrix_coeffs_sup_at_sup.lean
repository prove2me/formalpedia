-- Prove2me | solution 1 for Matrix.coeffs_sup_at_sup
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:49:51.780274+00:00
-- url     : https://prove2.me/submissions/8f16285d-ee82-4d44-87fd-9ee04a6be9e9

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
namespace Matrix
theorem _root_.solution (g : Matrix n m R) :
    v (g (g.coeffs_sup_at v).1 (g.coeffs_sup_at v).2) = g.coeffs_sup v :=
  (g.coeffs_sup_exists_repr v).choose_spec
end Matrix
