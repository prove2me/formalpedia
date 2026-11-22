-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_smul_toSubmodule
-- name    : Matrix.GeneralLinearGroup.smul_toSubmodule
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:49:50.304275+00:00
-- url     : https://prove2.me/theorems/f8571ca6-bca9-4111-a5f9-5579ef918e33
-- title:
--   General Linear Group: smul to Submodule
-- statement:
--   The General Linear Group construction uses the smul to Submodule property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L522-L525
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L522-L525

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
variable {ι : Type*} [DecidableEq ι] [Fintype ι]
variable {K : Type*} [CommRing K]
variable {R : Subring K}

theorem Matrix.GeneralLinearGroup.smul_toSubmodule (g h : GL ι K) :
    g • (h.toSubmodule (R := R)) = (g * h).toSubmodule (R := R) := by sorry
