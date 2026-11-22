-- Prove2me | Theorems.Thm_Matrix_coeffs_unique
-- name    : Matrix.coeffs_unique
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:20.124179+00:00
-- url     : https://prove2.me/theorems/c785ce90-d7a6-4cf0-90ad-d9765777db08
-- title:
--   Matrix: coeffs unique
-- statement:
--   The Matrix construction uses the coeffs unique property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L97-L100
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L97-L100

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

theorem Matrix.coeffs_unique [Unique n] [Unique m] (g : Matrix n m R) :
    g.coeffs = {g default default} := by sorry
