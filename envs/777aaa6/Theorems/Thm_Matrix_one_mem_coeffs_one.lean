-- Prove2me | Theorems.Thm_Matrix_one_mem_coeffs_one
-- name    : Matrix.one_mem_coeffs_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:51:23.245361+00:00
-- url     : https://prove2.me/theorems/e9033640-5473-49ee-a9b0-f855ae15efab
-- title:
--   Matrix: one mem coeffs one
-- statement:
--   The Matrix construction uses the one mem coeffs one property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L90-L95
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/Matrix.lean#L90-L95

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

theorem Matrix.one_mem_coeffs_one [One R] [Zero R] [Nonempty n] [DecidableEq n] :
    1 ∈ (1 : Matrix n n R).coeffs := by sorry
