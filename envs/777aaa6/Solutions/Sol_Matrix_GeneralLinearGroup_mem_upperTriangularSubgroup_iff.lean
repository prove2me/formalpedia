-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:48:47.139068+00:00
-- url     : https://prove2.me/submissions/8b163647-2ca0-439b-8ddd-859d6f768e04

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
namespace Matrix
namespace GeneralLinearGroup
theorem _root_.solution (R : Type*) [CommRing R] (ι : Type*)
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (g : GL ι R) :
    g ∈ GeneralLinearGroup.upperTriangularSubgroup R ι ↔
      g.val.BlockTriangular id :=
  .rfl
end GeneralLinearGroup
end Matrix
