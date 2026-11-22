-- Prove2me | Theorems.Thm_Matrix_GeneralLinearGroup_toLin_symm_apply
-- name    : Matrix.GeneralLinearGroup.toLin_symm_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:43:05.555116+00:00
-- url     : https://prove2.me/theorems/4f6bcfa0-607b-4e94-b305-963fc45476eb
-- title:
--   General Linear Group: to Lin symm apply
-- statement:
--   The General Linear Group construction uses the to Lin symm apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L266-L271
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/LinearAlgebra.lean#L266-L271

import Mathlib
import Definitions.Def_BruhatTits_Utils_Subring
import Definitions.Def_BruhatTits_Utils_LinearAlgebra
set_option autoImplicit false

theorem Matrix.GeneralLinearGroup.toLin_symm_apply {n : Type*} [DecidableEq n]
    [Fintype n] {R : Type*} [CommRing R] (g : LinearMap.GeneralLinearGroup R (n → R))
    (x : n → R) :
    (Matrix.GeneralLinearGroup.toLin.symm g).val.mulVec x = g.val x := by sorry
