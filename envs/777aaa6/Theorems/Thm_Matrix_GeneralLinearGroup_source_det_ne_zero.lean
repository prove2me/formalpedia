-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_source_det_ne_zero
-- name    : Matrix.GeneralLinearGroup.source_det_ne_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:53:45.015517+00:00
-- url     : https://prove2.me/theorems/f6a02c4b-84a4-49d3-912e-09fb2bde2257
-- title:
--   General Linear Group: source det ne zero
-- statement:
--   The General Linear Group construction uses the source det ne zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L380-L381
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L380-L381

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

theorem Matrix.GeneralLinearGroup.source_det_ne_zero [Nontrivial R] (g : GL n R) : g.val.det ≠ 0 := by sorry
