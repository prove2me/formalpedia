-- Prove2me | Theorems.Thm_Basis_ofIsBasisOn_apply
-- name    : Basis.ofIsBasisOn_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:49.320663+00:00
-- url     : https://prove2.me/theorems/daf4be49-4258-4152-9883-3a9782dcb143
-- title:
--   Basis: of Is Basis On apply
-- statement:
--   The Basis construction uses the of Is Basis On apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/IsBasisOn.lean#L97-L99
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/IsBasisOn.lean#L97-L99

import Definitions.Def_BruhatTits_Utils_Subring
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Definitions.Def_BruhatTits_Utils_IsBasisOn
set_option autoImplicit false
variable {R K V ι : Type*} [CommSemiring R] [Semiring K] [Algebra R K]
  [AddCommMonoid V] [Module R V] [Module K V] [IsScalarTower R K V]
open IsBasisOn

theorem Basis.ofIsBasisOn_apply (b : ι → V) (M : Submodule R V) [IsBasisOn b M] (i : ι) :
    ofIsBasisOn b M i = b i := by sorry
