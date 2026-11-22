-- Prove2me | Theorems.Thm_BruhatTits_smul_lt_iff
-- name    : BruhatTits.smul_lt_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T09:52:08.622672+00:00
-- url     : https://prove2.me/theorems/665a9783-4f92-4e62-a87b-7babcd1b7cdc
-- title:
--   Bruhat Tits: smul lt iff
-- statement:
--   The Bruhat Tits construction uses the smul lt iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L56-L65
-- source:
--   https://github.com/chrisflav/bruhat-tits/blob/1d61dd553feb2d1ed35c249298304b818765779c/BruhatTits/Utils/GLSubmoduleAction.lean#L56-L65

import Definitions.Def_BruhatTits_Utils_Matrix
import Definitions.Def_BruhatTits_Utils_GLSubmoduleAction
set_option autoImplicit false
variable {K : Type*} [Field K]
variable {R : Subring K}
open BruhatTits
open Pointwise
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem BruhatTits.smul_lt_iff (g : GL ι K) (M L : Submodule R (ι → K)) : g • M < g • L ↔ M < L := by sorry
