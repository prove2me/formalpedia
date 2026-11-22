-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_mem_upperTriangularSubgroup_iff
-- name    : Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:48:38.832579+00:00
-- url     : https://prove2.me/theorems/09d264e7-77fa-4899-bfd7-163553b8771f
-- title:
--   General Linear Group: mem upper Triangular Subgroup iff
-- statement:
--   The General Linear Group construction uses the mem upper Triangular Subgroup iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L600-L604
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L600-L604

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

theorem Matrix.GeneralLinearGroup.mem_upperTriangularSubgroup_iff (R : Type*) [CommRing R] (ι : Type*)
    [Fintype ι] [DecidableEq ι] [LinearOrder ι] (g : GL ι R) :
    g ∈ GeneralLinearGroup.upperTriangularSubgroup R ι ↔
      g.val.BlockTriangular id := by sorry
