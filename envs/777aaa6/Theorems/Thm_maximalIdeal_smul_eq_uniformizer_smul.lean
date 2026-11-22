-- Prove2me | Theorems.Thm_maximalIdeal_smul_eq_uniformizer_smul
-- name    : maximalIdeal_smul_eq_uniformizer_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:44:30.282195+00:00
-- url     : https://prove2.me/theorems/46266594-8842-4ba8-a839-888d379faab6
-- title:
--   maximal Ideal smul eq uniformizer smul: maximal Ideal smul eq uniformizer smul
-- statement:
--   The maximal Ideal smul eq uniformizer smul construction uses the maximal Ideal smul eq uniformizer smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L15-L19
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/ValuationRings.lean#L15-L19

import Mathlib
import Definitions.Def_BruhatTits_Utils_Misc
import Definitions.Def_BruhatTits_Utils_ValuationRings
set_option autoImplicit false
variable {K : Type*} [Field K] (R : Subring K)
variable {R}
open Pointwise

theorem maximalIdeal_smul_eq_uniformizer_smul [IsDiscreteValuationRing R] {ι : Type*} [Fintype ι]
    (M : Submodule R (ι → K)) {ϖ : R} (hϖ : Irreducible ϖ) :
    IsLocalRing.maximalIdeal R • M = ϖ • M := by sorry
