-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_apply_ne_zero_of_isDiag
-- name    : Matrix.GeneralLinearGroup.apply_ne_zero_of_isDiag
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:56.722425+00:00
-- url     : https://prove2.me/theorems/4a1c1237-c514-408f-8f36-3ff7b74d4bbb
-- title:
--   General Linear Group: apply ne zero of is Diag
-- statement:
--   The General Linear Group construction uses the apply ne zero of is Diag property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L383-L392
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L383-L392

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

theorem Matrix.GeneralLinearGroup.apply_ne_zero_of_isDiag [Nontrivial R] (g : GL n R) (h : g.val.IsDiag)
    (j : n) : g j j ≠ 0 := by sorry
