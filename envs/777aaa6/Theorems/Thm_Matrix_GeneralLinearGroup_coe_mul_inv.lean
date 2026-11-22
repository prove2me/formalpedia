-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_coe_mul_inv
-- name    : Matrix.GeneralLinearGroup.coe_mul_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:53:54.809769+00:00
-- url     : https://prove2.me/theorems/d8217fe1-92ec-49f5-9246-d4e4f85e064d
-- title:
--   General Linear Group: coe mul inv
-- statement:
--   The General Linear Group construction uses the coe mul inv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L394-L395
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L394-L395

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

theorem Matrix.GeneralLinearGroup.coe_mul_inv (g : GL n R) : g.val * g.val⁻¹ = 1 := by sorry
