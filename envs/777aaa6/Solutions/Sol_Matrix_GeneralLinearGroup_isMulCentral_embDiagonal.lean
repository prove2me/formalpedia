-- Prove2me | solution 1 for Matrix.GeneralLinearGroup.isMulCentral_embDiagonal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T09:53:45.277191+00:00
-- url     : https://prove2.me/submissions/448234a1-71cf-4cda-8a9f-540b6404e00a

import Definitions.Def_BruhatTits_Utils_RingHom
import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.RingTheory.Valuation.ValuationRing
import Mathlib.LinearAlgebra.Matrix.IsDiag
import Mathlib.LinearAlgebra.Matrix.Swap
import Mathlib.LinearAlgebra.Matrix.Block
import Definitions.Def_BruhatTits_Utils_Matrix
import Theorems.Thm_Matrix_GL_isMulCentral_diagonal

set_option autoImplicit false
open BigOperators
open Matrix
variable {R : Type*}
variable {n m n' m' : Type*}
variable [CommRing R]
variable [DecidableEq n] [Fintype n]
variable [DecidableEq m] [Fintype m]
open Matrix.GeneralLinearGroup
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}
namespace Matrix.GeneralLinearGroup
theorem _root_.solution {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    (u : Rˣ) :
    IsMulCentral (Matrix.GeneralLinearGroup.embDiagonal R ι u) :=
  Matrix.GL.isMulCentral_diagonal u
end Matrix.GeneralLinearGroup
