-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.source_det_ne_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T10:00:45.579179+00:00
-- url     : https://prove2.me/submissions/b92e59bc-e71a-4a08-89d2-439c450d9fda

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
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
open Matrix.GeneralLinearGroup
namespace Matrix.GeneralLinearGroup
theorem _root_.solution [Nontrivial R] (g : GL n R) : g.val.det ≠ 0 :=
  Units.ne_zero (det g)
end Matrix.GeneralLinearGroup
