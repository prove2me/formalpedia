-- Prove2me | Theorems.Thm_Matrix_BlockTriangular_fin_two_iff
-- name    : Matrix.BlockTriangular.fin_two_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:43.705395+00:00
-- url     : https://prove2.me/theorems/585a1f4f-3dfd-4f90-ad6e-2cbce8ffb8db
-- title:
--   Block Triangular: fin two iff
-- statement:
--   The Block Triangular construction uses the fin two iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L607-L609
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L607-L609

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

theorem Matrix.BlockTriangular.fin_two_iff {R : Type*} [Zero R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.BlockTriangular id ↔ M 1 0 = 0 := by sorry
